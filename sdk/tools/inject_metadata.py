#!/usr/bin/env python
# SPDX-FileCopyrightText: 2024 Google LLC
# SPDX-License-Identifier: Apache-2.0


from struct import pack, unpack

import os
import os.path
import sys

from subprocess import Popen, PIPE
from shutil import copy2
from pbpack import ResourcePack


import stm32_crc

# Pebble App Metadata Struct
# These are offsets of the PebbleProcessInfo struct in src/fw/app_management/pebble_process_info.h
HEADER_ADDR = 0x0  # 8 bytes
STRUCT_VERSION_ADDR = 0x8  # 2 bytes
SDK_VERSION_ADDR = 0xA  # 2 bytes
APP_VERSION_ADDR = 0xC  # 2 bytes
LOAD_SIZE_ADDR = 0xE  # 2 bytes
OFFSET_ADDR = 0x10  # 4 bytes
CRC_ADDR = 0x14  # 4 bytes
NAME_ADDR = 0x18  # 32 bytes
COMPANY_ADDR = 0x38  # 32 bytes
ICON_RES_ID_ADDR = 0x58  # 4 bytes
JUMP_TABLE_ADDR = 0x5C  # 4 bytes
FLAGS_ADDR = 0x60  # 4 bytes
NUM_RELOC_ENTRIES_ADDR = 0x64  # 4 bytes
UUID_ADDR = 0x68  # 16 bytes
RESOURCE_CRC_ADDR = 0x78  # 4 bytes
RESOURCE_TIMESTAMP_ADDR = 0x7C  # 4 bytes
VIRTUAL_SIZE_ADDR = 0x80  # 2 bytes
STRUCT_SIZE_BYTES = 0x82

# Pebble App Flags
# These are PebbleAppFlags from src/fw/app_management/pebble_process_info.h
PROCESS_INFO_STANDARD_APP = 0
PROCESS_INFO_WATCH_FACE = 1 << 0
PROCESS_INFO_VISIBILITY_HIDDEN = 1 << 1
PROCESS_INFO_VISIBILITY_SHOWN_ON_COMMUNICATION = 1 << 2
PROCESS_INFO_ALLOW_JS = 1 << 3
PROCESS_INFO_HAS_WORKER = 1 << 4

# Max app size, including the struct and reloc table
# Note that even if the app is smaller than this, it still may be too big, as it needs to share this
# space with applib/ which changes in size from release to release.
MAX_APP_BINARY_SIZE = 0x10000

# This number is a rough estimate, but should not be less than the available space.
# Currently, app_state uses up a small part of the app space.
# See also APP_RAM in stm32f2xx_flash_fw.ld and APP in pebble_app.ld.
MAX_APP_MEMORY_SIZE = 24 * 1024

# This number is a rough estimate, but should not be less than the available space.
# Currently, worker_state uses up a small part of the worker space.
# See also WORKER_RAM in stm32f2xx_flash_fw.ld
MAX_WORKER_MEMORY_SIZE = 10 * 1024

ENTRY_PT_SYMBOL = "main"
JUMP_TABLE_ADDR_SYMBOL = "pbl_table_addr"
DEBUG = False
ABSOLUTE_RELOCATION_TYPES = ("R_ARM_ABS32",)


class InvalidBinaryError(Exception):
    pass


def inject_metadata(
    target_binary,
    target_elf,
    resources_file,
    timestamp,
    allow_js=False,
    has_worker=False,
):

    if target_binary[-4:] != ".bin":
        raise Exception(
            "Invalid filename <%s>! The filename should end in .bin" % target_binary
        )

    def get_nm_output(elf_file):
        nm_process = Popen(["arm-none-eabi-nm", elf_file], stdout=PIPE)
        # Popen.communicate returns a tuple of (stdout, stderr)
        nm_output = nm_process.communicate()[0].decode("utf8")

        if not nm_output:
            raise InvalidBinaryError()

        nm_output = [line.split() for line in nm_output.splitlines()]
        return nm_output

    def get_symbol_addr(nm_output, symbol):
        # nm output looks like the following...
        #
        #          U _ITM_registerTMCloneTable
        # 00000084 t jump_to_pbl_function
        #          U _Jv_RegisterClasses
        # 0000009c T main
        # 00000130 T memset
        #
        # We don't care about the lines that only have two columns, they're not functions.

        for sym in nm_output:
            if symbol == sym[-1] and len(sym) == 3:
                return int(sym[0], 16)

        raise Exception(
            "Could not locate symbol <%s> in binary! Failed to inject app metadata"
            % (symbol)
        )

    def get_elf_sections(elf_file):
        """returns ELF section metadata keyed by section name"""

        readelf_sections_process = Popen(
            ["arm-none-eabi-readelf", "--wide", "-S", elf_file], stdout=PIPE
        )
        readelf_sections_output = readelf_sections_process.communicate()[0].decode(
            "utf8"
        )

        # readelf -S output looks like the following...
        #
        # [Nr] Name              Type            Addr     Off    Size   ES Flg Lk Inf Al
        # [ 0]                   NULL            00000000 000000 000000 00      0   0  0
        # [ 1] .header           PROGBITS        00000000 008000 000082 00   A  0   0  1
        # [ 2] .text             PROGBITS        00000084 008084 0006be 00  AX  0   0  4
        # [ 3] .rel.text         REL             00000000 00b66c 0004d0 08     23   2  4
        # [ 4] .data             PROGBITS        00000744 008744 000004 00  WA  0   0  4
        # [ 5] .bss              NOBITS          00000748 008748 000054 00  WA  0   0  4

        sections = {}

        for line in readelf_sections_output.splitlines():
            if len(line) < 10:
                continue

            # Carve off the first column, since it sometimes has a space in it which screws up the
            # split.
            if "]" not in line:
                continue
            line = line[line.index("]") + 1 :]

            columns = line.split()
            if len(columns) < 7:
                continue

            try:
                addr = int(columns[2], 16)
                size = int(columns[4], 16)
            except ValueError:
                continue

            sections[columns[0]] = {
                "type": columns[1],
                "addr": addr,
                "size": size,
                "flags": columns[6],
            }

        return sections, readelf_sections_output

    def get_virtual_size(elf_file):
        """returns the virtual size (highest allocated ELF section end) in bytes"""

        sections, readelf_sections_output = get_elf_sections(elf_file)
        last_alloc_section_end_addr = 0

        # The app heap starts at load_address + virtual_size. Account for every
        # allocated section so compiler-emitted sections after .data/.bss, such
        # as .got/.got.plt, remain app-owned memory instead of heap space.
        for section in sections.values():
            if "A" not in section["flags"]:
                continue

            last_alloc_section_end_addr = max(
                last_alloc_section_end_addr, section["addr"] + section["size"]
            )

        if last_alloc_section_end_addr != 0:
            return last_alloc_section_end_addr

        sys.stderr.write(
            "Failed to parse ELF sections while calculating the virtual size\n"
        )
        sys.stderr.write(readelf_sections_output)
        raise Exception(
            "Failed to parse ELF sections while calculating the virtual size"
        )

    def get_relocate_entries(elf_file):
        """returns a list of all the locations requiring an offset"""
        # TODO: insert link to the wiki page I'm about to write about PIC and relocatable values
        entries = []
        seen_entries = set()
        sections, _ = get_elf_sections(elf_file)

        def add_entry(addr):
            if addr not in seen_entries:
                seen_entries.add(addr)
                entries.append(addr)

        def get_relocation_target_section(relocation_section):
            if relocation_section.startswith(".rela"):
                return relocation_section[len(".rela") :]
            if relocation_section.startswith(".rel"):
                return relocation_section[len(".rel") :]
            return None

        def should_relocate_target_section(section_name):
            section = sections.get(section_name)
            if section is None:
                return False
            if section["type"] == "NOBITS":
                return False
            return "A" in section["flags"]

        # Generate runtime relocations from real ELF relocation records wherever
        # possible. Only absolute word relocations need the app load address
        # added by the firmware loader; PC-relative calls/jumps and GOT-relative
        # instruction fixups are already position-independent after link.
        readelf_relocs_process = Popen(
            ["arm-none-eabi-readelf", "--wide", "-r", elf_file], stdout=PIPE
        )
        readelf_relocs_output = readelf_relocs_process.communicate()[0].decode("utf8")
        lines = readelf_relocs_output.splitlines()

        should_read_relocations = False
        for line in lines:
            if line.startswith("Relocation section '"):
                relocation_section = line.split("'", 2)[1]
                target_section = get_relocation_target_section(relocation_section)
                should_read_relocations = should_relocate_target_section(
                    target_section
                )
                continue

            if not should_read_relocations:
                continue

            columns = line.split()
            if len(columns) < 3:
                continue
            if columns[2] not in ABSOLUTE_RELOCATION_TYPES:
                continue

            try:
                add_entry(int(columns[0], 16))
            except ValueError:
                pass

        # Keep the legacy Global Offset Table fallback: final linked app ELFs do
        # not necessarily preserve .rel.got, but .got contains app-relative
        # pointer words that must be adjusted by the loader.
        got_section = sections.get(".got")
        if (
            got_section is not None
            and got_section["type"] != "NOBITS"
            and "A" in got_section["flags"]
        ):
            for i in range(
                got_section["addr"], got_section["addr"] + got_section["size"], 4
            ):
                add_entry(i)

        return sorted(entries)

    nm_output = get_nm_output(target_elf)

    try:
        app_entry_address = get_symbol_addr(nm_output, ENTRY_PT_SYMBOL)
    except:
        raise Exception("Missing app entry point! Must be `int main(void) { ... }` ")
    jump_table_address = get_symbol_addr(nm_output, JUMP_TABLE_ADDR_SYMBOL)

    reloc_entries = get_relocate_entries(target_elf)

    statinfo = os.stat(target_binary)
    app_load_size = statinfo.st_size

    if resources_file is not None:
        with open(resources_file, "rb") as f:
            pbpack = ResourcePack.deserialize(f, is_system=False)
            resource_crc = pbpack.get_content_crc()
    else:
        resource_crc = 0

    if DEBUG:
        copy2(target_binary, target_binary + ".orig")

    with open(target_binary, "r+b") as f:
        total_app_image_size = app_load_size + (len(reloc_entries) * 4)
        if total_app_image_size > MAX_APP_BINARY_SIZE:
            raise Exception(
                "App image size is %u (app %u relocation table %u). Must be smaller "
                "than %u bytes"
                % (
                    total_app_image_size,
                    app_load_size,
                    len(reloc_entries) * 4,
                    MAX_APP_BINARY_SIZE,
                )
            )

        def read_value_at_offset(offset, format_str, size):
            f.seek(offset)
            return unpack(format_str, f.read(size))

        app_bin = f.read()
        app_crc = stm32_crc.crc32(app_bin[STRUCT_SIZE_BYTES:])

        [app_flags] = read_value_at_offset(FLAGS_ADDR, "<L", 4)

        if allow_js:
            app_flags = app_flags | PROCESS_INFO_ALLOW_JS

        if has_worker:
            app_flags = app_flags | PROCESS_INFO_HAS_WORKER

        app_virtual_size = get_virtual_size(target_elf)

        struct_changes = {
            "load_size": app_load_size,
            "entry_point": "0x%08x" % app_entry_address,
            "symbol_table": "0x%08x" % jump_table_address,
            "flags": app_flags,
            "crc": "0x%08x" % app_crc,
            "num_reloc_entries": "0x%08x" % len(reloc_entries),
            "resource_crc": "0x%08x" % resource_crc,
            "timestamp": timestamp,
            "virtual_size": app_virtual_size,
        }

        def write_value_at_offset(offset, format_str, value):
            f.seek(offset)
            f.write(pack(format_str, value))

        write_value_at_offset(LOAD_SIZE_ADDR, "<H", app_load_size)
        write_value_at_offset(OFFSET_ADDR, "<L", app_entry_address)
        write_value_at_offset(CRC_ADDR, "<L", app_crc)

        write_value_at_offset(RESOURCE_CRC_ADDR, "<L", resource_crc)
        write_value_at_offset(RESOURCE_TIMESTAMP_ADDR, "<L", timestamp)

        write_value_at_offset(JUMP_TABLE_ADDR, "<L", jump_table_address)

        write_value_at_offset(FLAGS_ADDR, "<L", app_flags)

        write_value_at_offset(NUM_RELOC_ENTRIES_ADDR, "<L", len(reloc_entries))

        write_value_at_offset(VIRTUAL_SIZE_ADDR, "<H", app_virtual_size)

        # Write the reloc_entries past the end of the binary. This expands the size of the binary,
        # but this new stuff won't actually be loaded into ram.
        f.seek(app_load_size)
        for entry in reloc_entries:
            f.write(pack("<L", entry))

        f.flush()

    return struct_changes
