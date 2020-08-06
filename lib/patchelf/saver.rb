# frozen_string_literal: true

require 'elftools/constants'
require 'elftools/elf_file'
require 'elftools/structs'
require 'elftools/util'
require 'patchelf/helper'
require 'fileutils'

module ELFTools
  module Constants
    module PF
      PF_X = 1
      PF_W = 2
      PF_R = 4
    end
    include PF

    module SHN
      SHN_UNDEF     =	0      # undefined section
      SHN_LORESERVE = 0xff00 # start of reserved indices
      SHN_HIRESERVE = 0xffff # end of reserved indices
    end
    include SHN

    module DT
      DT_VERSYM	= 0x6ffffff0
      # Ugly hack cped as is from patchelf, used to ignore DT_RUNPATH when DT_RPATH is forced.
      DT_IGNORE = 0x00726e67
    end
    include DT
  end
end

module PatchELF
  # Internal use only.
  #
  # For {Patcher} to do patching things and save to file.
  # @private
  class Saver
    # using ELFTools
    attr_reader :in_file # @return [String] Input filename.
    attr_reader :out_file # @return [String] Output filename.

    # Instantiate a {Saver} object.
    # @param [String] in_file
    # @param [String] out_file
    # @param [{Symbol => String, Array}] set
    def initialize(in_file, out_file, set)
      @in_file = in_file
      @out_file = out_file
      @set = set
      f = File.open(in_file, 'rb+')
      @elf = ELFTools::ELFFile.new(f)
      @buffer = StringIO.new(f.tap(&:rewind).read) # StringIO makes easier to work with Bindata

      @section_alignment = ehdr.e_phoff.num_bytes

      @segments = @elf.segments # usage similar to phdrs
      @sections = @elf.sections # usage similar to shdrs
      # {String => String}
      # section name to its data mapping
      @replaced_sections = {}
    end

    # @return [void]
    def save!
      @set.each { |mtd, _| send :"modify_#{mtd}" }
      rewrite_sections

      FileUtils.cp(in_file, out_file) if out_file != in_file
      patch_out
      # Let output file have the same permission as input.
      FileUtils.chmod(File.stat(in_file).mode, out_file)
    end

    private

    def ehdr
      @elf.header
    end

    def page_size
      PatchELF::Helper::PAGE_SIZE
    end

    # size is include NUL byte
    def replace_section(section, size)
      s = (@replaced_sections[section] || @sections.find { |sc| sc.name == section }.data)
      rs = if s.size == size
             s
           elsif s.size < size
             s.ljust(size, "\x00")
           else
             s[0...size] + "\x00"
           end
      @replaced_sections[section] = rs
    end

    def modify_interpreter
      @replaced_sections['.interp'] = @set[:interpreter] + "\x00"
    end

    def modify_needed
      nil
    end

    def buf_cstr(off)
      cstr = []
      with_buf_at(off) do |buf|
        loop do
          c = buf.read 1
          break if c.nil? || c == "\x00"

          cstr.push c
        end
      end
      cstr.join
    end

    def dynstr
      @sections.find { |s| s.name == '.dynstr' }
    end

    def modify_runpath
      nil
    end

    def modify_rpath(rpath_sym: :rpath)
      force_rpath = rpath_sym == :rpath
      new_rpath = @set[rpath_sym]

      dyn_rpath = dyn_runpath = nil
      needed_libs = []
      shdr_dynstr = dynstr&.header
      strtab_off = shdr_dynstr.sh_offset
      rpath_off = nil

      dyn_num_bytes = nil
      dt_null_idx = 0
      each_dynamic_tags do |dyn, _off|
        case dyn.d_tag
        when ELFTools::Constants::DT_RPATH
          dyn_rpath = dyn
          rpath_off = strtab_off + dyn.d_val if dyn_runpath.nil?
        when ELFTools::Constants::DT_RUNPATH
          dyn_runpath = dyn
          rpath_off = strtab_off + dyn.d_val
        when ELFTools::Constants::DT_NEEDED
          needed_libs.push buf_cstr(strtab_off + dyn.d_val)
        end
        dyn_num_bytes ||= dyn.num_bytes
        dt_null_idx += 1
      end
      old_rpath = rpath_off ? buf_cstr(rpath_off) : ''
      return if old_rpath == new_rpath

      with_buf_at(rpath_off) { |b| b.write('X' * old_rpath.size) } if rpath_off

      if !force_rpath && dyn_rpath && dyn_runpath.nil?
        dyn_rpath.d_tag = ELFTools::Constants::DT_RUNPATH
        dyn_runpath = dyn_rpath
        dyn_rpath = nil
      end

      dyn_runpath.d_tag = ELFTools::Constants::DT_IGNORE if force_rpath && dyn_rpath && dyn_runpath

      if new_rpath.size <= old_rpath.size
        with_buf_at(rpath_off) { |b| b.write new_rpath }
        return
      end

      PatchELF::Logger.info 'rpath is too long, resizing...'
      new_dynstr = replace_section '.dynstr', shdr_dynstr.sh_size + new_rpath.size + 1
      new_dynstr[(shdr_dynstr.sh_size.to_i)..(new_dynstr.size)] = "#{new_rpath}\x00"

      dyn_runpath.d_val = shdr_dynstr.sh_size.to_i if dyn_runpath
      dyn_rpath.d_val = shdr_dynstr.sh_size.to_i if dyn_rpath

      return if dyn_rpath || dyn_runpath

      # allot for new dt_runpath
      shdr_dynamic = @sections.find { |sec| sec.name == '.dynamic' }&.header
      new_dynamic_data = replace_section '.dynamic', shdr_dynamic.sh_size + dyn_num_bytes

      # consider DT_NULL when copying
      replacement_size = dyn_num_bytes * dt_null_idx.succ

      # make space for dt_runpath tag at the top, shift data by one tag positon
      new_dynamic_data[dyn_num_bytes..(replacement_size + dyn_num_bytes)] = new_dynamic_data[0..replacement_size]

      dyn_rpath = ELFTools::Structs::ELF_Dyn.new endian: shdr_dynamic.class.self_endian, class: shdr_dynamic.elf_class
      dyn_rpath.d_tag = force_rpath ? ELFTools::Constants::DT_RPATH : ELFTools::Constants::DT_RUNPATH
      dyn_rpath.d_val = dyn_num_bytes

      zi = StringIO.new
      dyn_rpath.write zi
      zi.rewind
      new_dynamic_data[0..dyn_num_bytes] = zi.read
    end

    def modify_soname
      return unless ehdr.e_type == ELFTools::Constants::ET_DYN

      #   shdr_dynstr = @sections.find { |s| s.name == '.dynstr' }&.header
      #   strtab_pos = shdr_dynstr.sh_offset

      #   dyn_soname = nil
      #   each_dynamic_tags do |dyn|
      #     dyn_soname = dyn if dyn.d_tag == ELFTools::Constants::DT_SONAME
      #   end

      #   if dyn_soname
      #     with_buf_at(strtab_pos + dyn_soname.d_val) do |buf|
      #       soname = []
      #       loop do
      #         c = buf.read 1
      #         break if c.nil? || c == "\x00"

      #         soname << c
      #       end
      #       PatchELF::Logger.info "soname = #{soname}"
      #     end
      #   end
    end

    def with_buf_at(pos)
      return unless block_given?

      opos = @buffer.tell
      @buffer.seek pos
      res = yield @buffer
      @buffer.seek opos
      res
    end

    def grow_file(newsz)
      bufsz = @buffer.size
      return if newsz <= bufsz

      @buffer.truncate newsz
    end

    def buf_move!(dst_idx, src_idx, n_bytes)
      with_buf_at(0) do |buf|
        tmp = buf.read
        tmp[dst_idx...(dst_idx + n_bytes)] = tmp[src_idx...(src_idx + n_bytes)]
        buf.truncate 0
        buf.rewind
        buf.write tmp
      end
    end

    def shift_file(extra_pages, start_page)
      oldsz = @buffer.size
      shift = extra_pages * page_size
      grow_file(oldsz + shift)

      buf_move! shift, 0, oldsz
      with_buf_at(ehdr.num_bytes) { |buf| buf.write "\x00" * (shift - ehdr.num_bytes) }

      ehdr.e_phoff = ehdr.num_bytes
      ehdr.e_shoff = ehdr.e_shoff + shift

      @sections.each_with_index do |sec, i|
        next if i.zero? # dont touch NULL section

        shdr = sec.header
        shdr.sh_offset += shift
      end

      @segments.each do |seg|
        phdr = seg.header
        phdr.p_offset += shift
        phdr.p_align = page_size if phdr.p_align != 0 && (phdr.p_vaddr - phdr.p_offset) % phdr.p_align != 0
      end

      ehdr.e_phnum += 1
      phdr = ELFTools::Structs::ELF_Phdr[@elf.elf_class].new(
        endian: @elf.endian,
        p_type: ELFTools::Constants::PT_LOAD,
        p_offset: 0,
        p_vaddr: start_page,
        p_paddr: start_page,
        p_filesz: shift,
        p_memsz: shift,
        p_flags: ELFTools::Constants::PF_R | ELFTools::Constants::PF_W,
        p_align: page_size
      )
      # no stream
      @segments.push ELFTools::Segments::Segment.new(phdr, nil)

      with_buf_at(0) { |b| ehdr.write(b) }
    end

    def sort_shdrs!
      rel_syms = [ELFTools::Constants::SHT_REL, ELFTools::Constants::SHT_RELA]

      # Translate sh_link mappings to section names, since sorting the
      # sections will invalidate the sh_link fields.
      # similar for sh_info
      linkage, info = @sections.each_with_object([{}, {}]) do |s, (link, info)|
        hdr = s.header
        link[s.name] = @sections[hdr.sh_link].name if hdr.sh_link.nonzero?
        info[s.name] = @sections[hdr.sh_info].name if hdr.sh_info.nonzero? && rel_syms.include?(hdr.sh_type)
      end
      shstrtab_name = @sections[ehdr.e_shstrndx].name

      @sections.sort! { |me, you| me.header.sh_offset.to_i <=> you.header.sh_offset.to_i }

      # restore sh_info, sh_link
      @sections.each do |sec|
        hdr = sec.header
        hdr.sh_link = @sections.find_index { |s| s.name == linkage[sec.name] } if hdr.sh_link.nonzero?
        if hdr.sh_info.nonzero? && rel_syms.include?(hdr.sh_type)
          info_sec_name = info[sec.name]
          hdr.sh_info = @sections.find_index { |s| s.name == info_sec_name }
        end
      end

      ehdr.e_shstrndx = @sections.find_index { |s| s.name == shstrtab_name }
    end

    def sort_phdrs!
      pt_phdr = ELFTools::Constants::PT_PHDR
      @segments.sort! do |me, you|
        next  1 if you.header.p_type == pt_phdr
        next -1 if me.header.p_type == pt_phdr

        me.header.p_paddr.to_i <=> you.header.p_paddr.to_i
      end
    end

    def rewrite_sections_executable
      seg_num_bytes = @segments.first.header.num_bytes
      sort_shdrs!
      last_replaced = 0

      # PatchELF::Logger.info @sections.first.name

      @sections.each_with_index { |sec, idx| last_replaced = idx if @replaced_sections[sec.name] }
      raise PatchELF::PatchError, 'last_replaced = 0' if last_replaced.zero?
      raise PatchELF::PatchError, 'last_replaced + 1 >= @sections.size' if last_replaced + 1 >= @sections.size

      # PatchELF::Logger.info "last replaced = #{last_replaced}"

      start_replacement_hdr = @sections[last_replaced + 1].header
      start_offset = start_replacement_hdr.sh_offset
      start_addr = start_replacement_hdr.sh_addr

      prev_sec_name = ''
      (1..last_replaced).each do |idx|
        sec = @sections[idx]
        shdr = sec.header
        if (sec.type == ELFTools::Constants::SHT_PROGBITS && sec.name != '.interp') || prev_sec_name == '.dynstr'
          start_addr = shdr.sh_addr
          start_offset = shdr.sh_offset
          last_replaced = idx - 1
          break
        elsif @replaced_sections[sec.name].nil?
          # get blocking section out of the way
          replace_section(sec.name, shdr.sh_size)
        end

        prev_sec_name = sec.name
      end

      unless start_addr % page_size == start_offset % page_size
        raise PatchELF::PatchError, 'start_addr /= start_offset (mod PAGE_SIZE)'
      end

      first_page = start_addr - start_offset

      if ehdr.e_shoff < start_offset
        shoff_new = @buffer.size
        sh_size = ehdr.e_shoff + ehdr.e_shnum * ehdr.e_shentsize
        grow_file @buffer.size + sh_size
        ehdr.e_shoff = shoff_new
        raise PatchELF::PatchError, 'ehdr.e_shnum /= @sections.size' unless ehdr.e_shnum == @sections.size

        with_buf_at(e_shoff + @sections.first.header.num_bytes) do |buf| # skip writing to NULL section
          @sections.each_with_index do |sec, idx|
            next if idx.zero?

            sec.header.write buf
          end
        end
      end

      needed_space = (
        ehdr.num_bytes +
        (@segments.count * seg_num_bytes) +
        @replaced_sections.sum { |_, str| PatchELF::Helper.alignup(str.size, @section_alignment) }
      )

      if needed_space > start_offset
        needed_space += seg_num_bytes # new load segment is required
        needed_pages = PatchELF::Helper.alignup(needed_space - start_offset, page_size) / page_size
        raise PatchELF::PatchError, 'virtual address space underrun' if needed_pages * page_size > first_page

        first_page -= needed_pages * page_size
        start_offset += needed_pages * page_size

        shift_file(needed_pages, first_page)
      end

      # PatchELF::Logger.info "needed space is #{needed_space}"

      cur_off = ehdr.num_bytes + (@segments.count * seg_num_bytes)
      with_buf_at(cur_off) { |buf| buf.write "\x00" * (start_offset - cur_off) }
      cur_off = write_replaced_sections cur_off, first_page, 0
      # PatchELF::Logger.info " cur_off = #{cur_off} "
      raise PatchELF::PatchError, 'cur_off /= needed_space' if cur_off != needed_space

      rewrite_headers first_page + ehdr.e_phoff
    end

    # yields dynamic tag, and offset in buffer
    def each_dynamic_tags
      return unless block_given?

      sec = @sections.find { |sec| sec.name == '.dynamic' }
      return unless sec

      shdr = sec.header
      with_buf_at(shdr.sh_offset) do |buf|
        dyn = ELFTools::Structs::ELF_Dyn.new(elf_class: shdr.elf_class, endian: shdr.class.self_endian)
        loop do
          buf_dyn_offset = buf.tell
          dyn.clear
          dyn.read(buf)
          break if dyn.d_tag == ELFTools::Constants::DT_NULL

          yield dyn, buf_dyn_offset
          # safety :*
          buf.seek buf_dyn_offset + dyn.num_bytes
        end
      end
    end

    def rewrite_headers(phdr_address)
      # there can only be a single program header table according to ELF spec
      @segments.find { |seg| seg.header.p_type == ELFTools::Constants::PT_PHDR }&.tap do |seg|
        phdr = seg.header
        phdr.p_offset = ehdr.e_phoff.to_i
        phdr.p_vaddr = phdr.p_paddr = phdr_address.to_i
        phdr.p_filesz = phdr.p_memsz = phdr.num_bytes * @segments.count # e_phentsize * e_phnum
      end

      sort_phdrs!

      # with_buf_at(ehdr.e_phoff) do |buf|
      #   @segments.each { |seg| seg.header.write(buf) }
      # end
      raise PatchELF::PatchError, 'ehdr.e_shnum /= @sections.count' unless ehdr.e_shnum == @sections.count

      sort_shdrs!
      # with_buf_at(ehdr.e_shoff) do |buf|
      #   @sections.each { |section| section.header.write(buf) }
      # end

      each_dynamic_tags do |dyn, buf_off|
        case dyn.d_tag
        when ELFTools::Constants::DT_STRTAB
          dyn.d_val = @sections.find { |s| s.name == '.dynstr' }.header.sh_addr.to_i
        when ELFTools::Constants::DT_STRSZ
          dyn.d_val = @sections.find { |s| s.name == '.dynstr' }.header.sh_size.to_i
        when ELFTools::Constants::DT_SYMTAB
          dyn.d_val = @sections.find { |s| s.name == '.dynsym' }.header.sh_addr.to_i
        when ELFTools::Constants::DT_HASH
          dyn.d_val = @sections.find { |s| s.name == '.hash' }.header.sh_addr.to_i
        when ELFTools::Constants::DT_GNU_HASH
          dyn.d_val = @sections.find { |s| s.name == '.gnu.hash' }.header.sh_addr.to_i
        when ELFTools::Constants::DT_JMPREL
          shdr = @sections.find { |s| %w[.rel.plt .rela.plt .rela.IA_64.pltoff].include? s.name }&.header
          raise PatchELF::PatchError, 'cannot find section corresponding to DT_JMPREL' if shdr.nil?

          dyn.d_val = shdr.sh_addr.to_i
        when ELFTools::Constants::DT_REL
          # regarding .rel.got, NixOS/patchelf says
          # "no idea if this makes sense, but it was needed for some program"
          shdr = @sections.find { |s| %w[.rel.dyn .rel.got].include? s.name }&.header
          next if shdr.nil? # patchelf claims no problem in skipping

          dyn.d_val = shdr.sh_addr.to_i
        when ELFTools::Constants::DT_RELA
          shdr = @sections.find { |s| s.name == '.rela.dyn' }&.header
          next if shdr.nil? # patchelf claims no problem in skipping

          dyn.d_val = shdr.sh_addr.to_i
        when ELFTools::Constants::DT_VERNEED
          dyn.d_val = @sections.find { |s| s.name == '.gnu.version_r' }.header.sh_addr.to_i
        when ELFTools::Constants::DT_VERSYM
          dyn.d_val = @sections.find { |s| s.name == '.gnu.version' }.header.sh_addr.to_i
        end

        with_buf_at(buf_off) { |wbuf| dyn.write(wbuf) }
      end

      symtabs = [ELFTools::Constants::SHT_SYMTAB, ELFTools::Constants::SHT_DYNSYM]
      @sections.each do |sec|
        shdr = sec.header
        next unless symtabs.include?(shdr.sh_type)

        sym = ELFTools::Structs::ELF_sym[ehdr.elf_class].new endian: shdr.class.self_endian
        with_buf_at(shdr.sh_offset) do |buf|
          sec.num_symbols.times do |entry|
            sym.clear
            sym.read(buf)

            shndx = sym.st_shndx
            next if shndx == ELFTools::Constants::SHN_UNDEF || shndx >= ELFTools::Constants::SHN_LORESERVE

            old_sections = @elf.sections
            if shndx >= old_sections.count
              PatchELF::Logger.warn "entry #{entry} in symbol table refers to a non existing section, skipping"
              next
            end

            old_sec = old_sections[shndx]
            raise PatchELF::PatchError, '@elf.sections[shndx] is nil' if old_sec.nil?

            new_index = @sections.find_index { |s| s.name == old_sec.name }
            sym.st_shndx = new_index
            # right 4 bits in the st_info field is st_type
            if (sym.st_info & 0xF) == ELFTools::Constants::STT_SECTION
              sym.st_value = @sections[new_index].header.sh_addr.to_i
            end

            with_buf_at(shdr.sh_offset + entry * sym.num_bytes) { |tbuf| sym.write(tbuf) }
          end
        end
      end
    end

    def write_replaced_sections(cur_off, start_addr, start_offset)
      sht_no_bits = ELFTools::Constants::SHT_NOBITS
      pt_interp = ELFTools::Constants::PT_INTERP
      pt_dynamic = ELFTools::Constants::PT_DYNAMIC

      # the original source says this has to be done seperately to
      # prevent clobbering the previously written section contents.
      @replaced_sections.each do |rsec_name, _|
        shdr = @sections.find { |s| s.name == rsec_name }.header
        with_buf_at(shdr.sh_offset) { |b| b.write('X' * shdr.sh_size) } if shdr.sh_type != sht_no_bits
      end

      @replaced_sections.each do |rsec_name, rsec_data|
        shdr = @sections.find { |s| s.name == rsec_name }.header

        with_buf_at(cur_off) { |b| b.write rsec_data }

        shdr.sh_offset = cur_off
        shdr.sh_addr = start_addr + (cur_off - start_offset)
        shdr.sh_size = rsec_data.size
        shdr.sh_addralign = @section_alignment

        if ['.interp', '.dynamic'].include? rsec_name
          seg_type = rsec_name == '.interp' ? pt_interp : pt_dynamic
          @segments.each do |seg|
            next unless (phdr = seg.header).p_type == seg_type

            phdr.p_offset = shdr.sh_offset.to_i
            phdr.p_vaddr = phdr.p_paddr = shdr.sh_addr.to_i
            phdr.p_filesz = phdr.p_memsz = shdr.sh_size.to_i
          end
        end

        cur_off += PatchELF::Helper.alignup(rsec_data.size, @section_alignment)
      end
      @replaced_sections.clear

      cur_off
    end

    def rewrite_sections_library
      start_page =
        @segments.map { |seg| PatchELF::Helper.alignup(seg.header.p_vaddr + seg.header.p_memsz, page_size) }
                 .max

      PatchELF::Logger.info "Last page is 0x#{start_page.to_s 16}"

      pht_size = ehdr.num_bytes + @segments.count.succ * @segments.first.header.num_bytes
      # replace sections that may overlap with expanded program header table
      @sections.each_with_index do |sec, idx|
        shdr = sec.header
        next if idx.zero? || @replaced_sections[sec.name]
        break if shdr.sh_addr > pht_size

        replace_section sec.name, shdr.sh_size
      end

      needed_space =
        @replaced_sections.sum { |_, str| PatchELF::Helper.alignup(str.size, @section_alignment) }
      PatchELF::Logger.info "needed space = #{needed_space}"

      start_offset = PatchELF::Helper.alignup(@buffer.size, page_size)
      grow_file start_offset + needed_space

      # executable shared object
      if @segments.any? { |seg| seg.header.p_type == ELFTools::Constants::PT_INTERP }
        if start_offset > start_page
          PatchELF::Logger.info(
            "shifting new PT_LOAD segment by #{start_offset - start_page} bytes to work around a Linux kernel bug"
          )
        end
        start_page = start_offset
      end

      ehdr.e_phnum += 1
      phdr = ELFTools::Structs::ELF_Phdr[@elf.elf_class].new(
        endian: @elf.endian,
        p_type: ELFTools::Constants::PT_LOAD,
        p_offset: start_offset,
        p_vaddr: start_page,
        p_paddr: start_page,
        p_filesz: needed_space,
        p_memsz: needed_space,
        p_flags: ELFTools::Constants::PF_R | ELFTools::Constants::PF_W,
        p_align: page_size
      )
      # no stream
      @segments.push ELFTools::Segments::Segment.new(phdr, nil)

      cur_off = write_replaced_sections start_offset, start_page, start_offset
      raise PatchELF::PatchError, 'cur_off /= start_offset+needed_space' if cur_off != start_offset + needed_space

      rewrite_headers ehdr.e_phoff
    end

    def rewrite_sections
      return if @replaced_sections.empty?

      case @elf.elf_type
      when 'DYN'
        rewrite_sections_library
      when 'EXEC'
        rewrite_sections_executable
      else
        raise PatchELF::PatchError, 'unknown ELF type'
      end
    end

    # Modify the out_file according to registered patches.
    def patch_out
      with_buf_at(0) { |b| ehdr.write(b) }

      shoff = ehdr.e_shoff
      with_buf_at(shoff) do |buf|
        @sections.each { |sec| sec.header.write buf }
      end

      phoff = ehdr.e_phoff
      with_buf_at(phoff) do |buf|
        @segments.each { |seg| seg.header.write buf }
      end

      File.open(out_file, 'wb+') do |f|
        @buffer.rewind
        f.write @buffer.read
      end
    end

    # @return [ELFTools::Sections::Section?]
    def section_header(name)
      sec = @elf.section_by_name(name)
      return if sec.nil?

      sec.header
    end

    def dynamic
      @dynamic ||= @elf.segment_by_type(:dynamic)
    end
  end
end
