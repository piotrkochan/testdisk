/*

    File: image_filter.h

    Copyright (C) 2024 Christophe GRENIER <grenier@cgsecurity.org>

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

#ifndef _IMAGE_FILTER_H
#define _IMAGE_FILTER_H

#ifdef __cplusplus
extern "C" {
#endif

#include "types.h"
#include <stdint.h>

struct image_size_filter_struct
{
  uint32_t min_width;      /* 0 = no limit */
  uint32_t max_width;      /* 0 = no limit */
  uint32_t min_height;     /* 0 = no limit */
  uint32_t max_height;     /* 0 = no limit */
  uint64_t min_pixels;     /* 0 = no limit (width × height) */
  uint64_t max_pixels;     /* 0 = no limit (width × height) */
};

typedef struct image_size_filter_struct image_size_filter_t;

int has_any_image_size_filter(void);
int should_skip_image_by_dimensions(uint32_t width, uint32_t height);

void change_imagesize_cli(char **cmd);

int validate_image_filter(void);

uint64_t parse_pixels_value(char **cmd);

void print_image_filter(void);

void parse_pixels_range(char **cmd, uint64_t *min_pixels, uint64_t *max_pixels);

void image_size_2_cli(char *buffer, size_t buffer_size);

// Global image filter functions
void set_global_image_filter(const image_size_filter_t *filter);
const image_size_filter_t* get_global_image_filter(void);

#ifdef __cplusplus
}
#endif
#endif