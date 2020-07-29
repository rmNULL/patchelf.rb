# frozen_string_literal: true

require 'elftools/constants'
require 'elftools/elf_file'
require 'elftools/structs'
require 'elftools/util'
require 'patchelf/helper'
require 'fileutils'

# module ELFTools
#   module Structs
#     [ELF32_Phdr, ELF64_Phdr].each do |cls|
#       refine cls do
#         include Comparable

#         def <=>(other)
#           return  1 if other.p_type == ELFTools::Constants::PT_PHDR
#           return -1 if p_type == ELFTools::Constants::PT_PHDR

#           p_paddr <=> other.p_paddr
#         end
#       end
#     end
#   end
# end

module ELFTools
  module Constants
    module PF
      PF_X rescue PF_X = 1
      PF_W rescue PF_W = 2
      PF_R rescue PF_R = 4
    end
    include PF
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
      @buffer = StringIO.new f.read
      @elf = ELFTools::ELFFile.new(@buffer)

      @section_alignment = @elf.header.e_phoff.num_bytes

      @segments = @elf.segments # usage similar to phdrs
      @sections = @elf.sections # usage similar to shdrs
      # {String => String}
      # section name to its string mapping
      @replaced_sections = {}
    end

    # @return [void]
    def save!
      @set.each { |mtd, _| send :"modify_#{mtd}" }

      FileUtils.cp(in_file, out_file) if out_file != in_file
      patch_out
      # Let output file have the same permission as input.
      FileUtils.chmod(File.stat(in_file).mode, out_file)
    end

    private

    def page_size
      PatchELF::Helper::PAGE_SIZE
    end

    # size is include NUL byte
    def replace_section(section, size)
      s = (@replaced_sections[:section] || @elf.section_by_name(section).data)
      rs = if s.size < size
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

    def modify_runpath
      nil
    end

    def modify_rpath
      nil
    end

    def modify_soname
      nil
    end

    def with_buf_at(pos)
      return unless block_given?

      opos = @buffer.tell
      @buffer.seek pos
      yield @buffer
      @buffer.seek opos
      @buffer
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
        buf.write buf
      end
    end

    def shift_file(extra_pages, start_page)
      ehdr = @elf.header
      oldsz = @buffer.size
      shift = extra_pages * page_size
      grow_file(oldsz + shift)

      buf_move! shift, 0, oldsz
      with_buf_at(ehdr.num_bytes) { |buf| buf.write "\x00" * (shift - ehdr.num_bytes) }

      ehdr.e_phoff = ehdr.num_bytes
      ehdr.e_shoff = ehdr.e_shoff + shift
      @sections.each { |sec| sec.header.sh_offset += shift }
      @segments.each do |seg|
        phdr = seg.header
        phdr.p_offset += shift
        phdr.p_align = page_size if phdr.p_align != 0 && (phdr.p_vaddr - phdr.p_offset) % phdr.p_align != 0
      end

      phdr = ELFTools::Structs::ELF_Phdr[e.elf_class].new(
        endian: e.endian,
        p_type: ELFTools::Constants::PT_LOAD,
        p_offset: 0,
        p_vaddr: start_page,
        p_paddr: start_page,
        p_filesz: shift,
        p_memsz: shift,
        p_flags: ELFTools::Constants::PF_R | ELFTools::Constants::PF_W,
        p_align: page_size
      )
      @segments.push ELFTools::Segments::Segments.new(phdr, @buffer)
    end

    def sort_shdrs
      rel_syms = [ELFTools::Constants::SHT_REL, ELFTools::Constants::SHT_RELA]

      # Translate sh_link mappings to section names, since sorting the
      # sections will invalidate the sh_link fields.
      # similar for sh_info
      linkage, info = @sections.each_with_object([{}, {}]) do |s, (link, info)|
        hdr = s.header
        link[s.name] = @sections[hdr.sh_link].name if hdr.sh_link.nonzero?
        info[s.name] = @sections[hdr.sh_info].name if hdr.sh_info.nonzero? && rel_syms.include?(hdr.sh_type)
      end
      shstrtab_name = @sections[@elf.header.e_shstrndx].name
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

      @elf.header.e_shstrndx = @sections.find_index { |s| s.name == shstrtab_name }
    end

    def rewrite_sections_executable
      ehdr = @elf.header
      sort_shdrs
      last_replaced = 0
      @sections.each_with_index { |sec, idx| last_replaced = idx if @replaced_sections[sec.name] }
      raise PatchELF::PatchError, 'failed, last_replaced + 1 < @sections.size' if last_replaced + 1 >= @sections.size

      last_replaced_hdr = @sections[last_replaced + 1]
      start_offset = last_replaced_hdr.sh_offset
      start_addr = last_replaced_hdr.sh_addr

      prev_sec_name = ''
      @sections.take(last_replaced + 1).each_with_index do |sec, idx|
        next if idx.zero?

        hdr = sec.header
        if (sec.type == ELFTools::Constants::SHT_PROGBITS && sec.name != '.interp') || prev_sec_name == '.dynstr'
          start_addr = hdr.sh_addr
          start_offset = hdr.sh_offset
          last_replaced = idx - 1
          break
        elsif @replaced_sections[sec.name]
          replace_section(sec_name, hdr.sh_size)
        end

        prev_sec_name = sec.name
      end

      unless start_addr % page_size == start_offset % page_size
        raise PatchELF::PatchError, 'start_addr /= start_offset (mod PAGE_SIZE)'
      end
      first_page = start_addr - start_offset

      if ehdr .e_shoff < start_offset
        shoff_new = @buffer.size
        sh_size = ehdr.e_shoff + ehdr.e_shnum * ehdr.e_shentsize
        grow_file @buffer.size + sh_size

        ehdr.e_shoff = shoff_new
        raise PatchELF::PatchError, 'ehdr.e_shnum /= @sections.size' unless ehdr.e_shnum == @sections.size

        opos = @buffer.tell
        @buffer.seek(e_shoff + @sections.first.header.num_bytes) # skip writing to NULL section
        @sections.each_with_index do |sec, idx|
          next if idx.zero?

          sec.header.write @buffer
        end
        @buffer.seek opos
      end

      seg_num_bytes = @segments.first.header.num_bytes
      needed_space = (
        ehdr.num_bytes +
        (@segments.count * seg_num_bytes) +
        @replaced_sections.sum { |_, str| PatchELF::Helper.alignup(str.size, @section_alignment) }
      )

      if needed_space > start_offset
        needed_space += seg_num_bytes
        needed_pages = PatchELF::Helper.alignup(needed_space - start_offset, page_size) / page_size
        raise PatchELF::PatchError, 'virtual address space underrun' if needed_pages * page_size > first_page

        first_page -= needed_pages * page_size
        start_offset += needed_pages * page_size

        shift_file(needed_pages, first_page)
      end

      cur_off = ehdr.num_bytes + (@segments.count * seg_num_bytes)
      with_buf_at(cur_off) { |buf| buf.write "\x00" * (start_offset - cur_off) }

      write_replaced_sections cur_off, first_page, 0
      raise PatchELF::PatchError, 'cur_off /= needed_space' unless cur_off != needed_space

      rewrite_headers first_page + ehdr.e_phoff
    end

    def rewrite_headers(phdr_address)
      nil
    end

    def write_replaced_sections(cur_off, start_addr, start_offset)
      nil
    end

    def rewrite_sections_library
      nil
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
