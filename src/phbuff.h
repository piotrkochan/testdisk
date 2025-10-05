/*

    File: phbuff.h

    Copyright (C) 2007-2009 Christophe GRENIER <grenier@cgsecurity.org>

    This software is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along
    with this program; if not, write the Free Software Foundation, Inc., 51
    Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

 */
#ifndef _PHOTOREC_PHBUFF_H
#define _PHOTOREC_PHBUFF_H

#ifdef __cplusplus
extern "C" {
#endif

#include "filegen.h"

// Memory buffering functions for file recovery
int file_buffer_write(file_recovery_t *file_recovery, const void *data, size_t size);
int file_buffer_flush(file_recovery_t *file_recovery);
int file_buffer_clear(file_recovery_t *file_recovery);
const unsigned char* file_buffer_get_data(file_recovery_t *file_recovery, size_t *buffer_size);
int read_file_data_from_buffer(file_recovery_t *file_recovery);
void flush_all_buffers(void);
void print_buffer_statistics(void);

// Global file size filter functions
void set_global_file_size_filter(const file_size_filter_t *filter);
uint64_t get_user_min_filesize(void);
uint64_t get_user_max_filesize(void);

#ifdef __cplusplus
} /* closing brace for extern "C" */
#endif

#endif /* _PHOTOREC_PHBUFF_H */