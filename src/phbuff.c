/*

    File: phbuff.c

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

#define _GNU_SOURCE // For fopencookie

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#ifdef HAVE_STDLIB_H
#include <stdlib.h>
#endif
#ifdef HAVE_STRING_H
#include <string.h>
#endif
#include <stdio.h>
#include <errno.h>
#ifdef HAVE_TIME_H
#include <time.h>
#endif
#include "types.h"
#include "common.h"
#include "filegen.h"
#include "photorec.h"
#include "log.h"
#include "phbuff.h"

// Memory buffer for each file recovery with hash table lookup
#define MAX_FILE_BUFFERS 30
#define HASH_TABLE_SIZE 31 // Prime number for better distribution

// Cookie structure for fopencookie - tracks position in buffer
typedef struct {
  int buffer_idx;      // Index into file_buffers array
  off64_t position;    // Current read position in buffer
} buffer_cookie_t;

// Enhanced statistics for monitoring buffer vs disk usage
static struct
{
  unsigned long buffer_writes;      // Successful buffer writes
  unsigned long disk_fallback_full; // Fallback due to buffer pool full
  unsigned long disk_fallback_size; // Fallback due to file too large
  unsigned long disk_fallback_oom;  // Fallback due to malloc/realloc failure
  unsigned long hash_collisions;    // NEW: Hash collision count
  unsigned long max_chain_length;   // NEW: Longest collision chain
  unsigned long memory_usage;       // NEW: Current memory usage
  unsigned long realloc_count;      // NEW: Number of buffer reallocations
} buffer_stats = {0, 0, 0, 0, 0, 0, 0, 0};

static struct
{
  file_recovery_t *file_recovery_ptr; // Use file_recovery pointer as stable key
  char filename[2048];                // Store filename copy to avoid segfaults
  unsigned char *buffer;
  size_t buffer_size;
  size_t buffer_capacity;
  FILE *read_handle;   // File handle for reading from buffer (fopencookie)
  FILE *save_handle;   // File handle for saving buffer to disk
  int next_index;      // For collision chaining, -1 means end of chain
  int already_flushed; // Flag to prevent double-writing
  int is_active;       // Mark if buffer slot is active (1) or free (0)
} file_buffers[MAX_FILE_BUFFERS];

static int hash_table[HASH_TABLE_SIZE]; // Index into file_buffers, -1 means empty

// OPTIMIZATION: Free list for fast buffer allocation
static int free_list_head = -1; // Head of free slots linked list, -1 means empty

// Global file size filter for all recovery operations (copy, not pointer!)
static file_size_filter_t global_file_size_filter = {0, 0};

// Fast simple hash function for performance
static int hash_file_recovery(file_recovery_t *file_recovery)
{
  uintptr_t ptr = (uintptr_t)file_recovery;
  uint32_t high = (uint32_t)(ptr >> 32);
  uint32_t low = (uint32_t)(ptr & 0xFFFFFFFF);
  unsigned int hash = high ^ low;
  return hash % HASH_TABLE_SIZE;
}

// Custom I/O functions for fopencookie - reading from memory buffer
static ssize_t buffer_read(void *cookie, char *buf, size_t size)
{
  buffer_cookie_t *bc = (buffer_cookie_t *)cookie;
  int idx = bc->buffer_idx;

  // Safety checks
  if (idx < 0 || idx >= MAX_FILE_BUFFERS || !file_buffers[idx].is_active)
    return -1;

  // Calculate how much can be read (not more than buffer_size)
  size_t available = file_buffers[idx].buffer_size - bc->position;
  size_t to_read = (size < available) ? size : available;

  if (to_read > 0)
  {
    memcpy(buf, file_buffers[idx].buffer + bc->position, to_read);
    bc->position += to_read;
  }

  return to_read; // Returns 0 when EOF (position >= buffer_size)
}

// Custom seek function - SEEK_END points to buffer_size (not capacity!)
static int buffer_seek(void *cookie, off64_t *offset, int whence)
{
  buffer_cookie_t *bc = (buffer_cookie_t *)cookie;
  int idx = bc->buffer_idx;

  // Safety checks
  if (idx < 0 || idx >= MAX_FILE_BUFFERS || !file_buffers[idx].is_active)
    return -1;

  off64_t new_pos;
  switch (whence)
  {
  case SEEK_SET:
    new_pos = *offset;
    break;
  case SEEK_CUR:
    new_pos = bc->position + *offset;
    break;
  case SEEK_END:
    new_pos = file_buffers[idx].buffer_size + *offset; // EOF = buffer_size!
    break;
  default:
    return -1;
  }

  // Clamp to [0, buffer_size]
  if (new_pos < 0)
    new_pos = 0;
  if ((size_t)new_pos > file_buffers[idx].buffer_size)
    new_pos = file_buffers[idx].buffer_size;

  bc->position = new_pos;
  *offset = new_pos;
  return 0;
}

// Custom close function - cleanup cookie
static int buffer_close(void *cookie)
{
  free(cookie);
  return 0;
}

// Initialize hash table (call once at startup)
static void init_buffer_hash_table(void)
{
  static int initialized = 0;
  if (!initialized)
  {
    for (int i = 0; i < HASH_TABLE_SIZE; i++)
    {
      hash_table[i] = -1;
    }
    // OPTIMIZATION: Build free list during initialization
    for (int i = 0; i < MAX_FILE_BUFFERS; i++)
    {
      file_buffers[i].next_index = (i + 1 < MAX_FILE_BUFFERS) ? i + 1 : -1; // Link to next free slot
      file_buffers[i].is_active = 0;
      file_buffers[i].file_recovery_ptr = NULL;
      file_buffers[i].filename[0] = '\0';
      file_buffers[i].buffer = NULL; // IMPORTANT: Initialize to NULL
      file_buffers[i].buffer_size = 0;
      file_buffers[i].buffer_capacity = 0;
      file_buffers[i].read_handle = NULL; // Initialize read_handle to NULL
      file_buffers[i].save_handle = NULL; // Initialize save_handle to NULL
      file_buffers[i].already_flushed = 0;
    }
    free_list_head = 0; // Point to first free slot
    initialized = 1;
  }
}

// Get buffer size based on file type hint only (NOT user filesize filter)
// Priority: file_hint->max_filesize > 1GB default
// HARD LIMIT: Never allocate more than 10GB
static uint64_t get_buffer_size_for_file(file_recovery_t *file_recovery)
{
  uint64_t type_max = 1024ULL * 1024 * 1024;        // 1GB default
  uint64_t hard_limit = 10ULL * 1024 * 1024 * 1024; // 10GB hard limit
  uint64_t result;

  // Get file type's max size if available
  if (file_recovery->file_stat &&
      file_recovery->file_stat->file_hint &&
      file_recovery->file_stat->file_hint->max_filesize > 0)
  {
    type_max = file_recovery->file_stat->file_hint->max_filesize;
  }

  result = type_max;

  // NEVER exceed 10GB hard limit
  if (result > hard_limit)
  {
    result = hard_limit;
  }

  return result;
}

// Check if user has filesize filters active
static int has_user_filesize_limits(void)
{
  return (global_file_size_filter.min_file_size > 0 ||
          global_file_size_filter.max_file_size > 0);
}

// IMPROVED: Buffer management with better error handling
static int get_buffer_index(file_recovery_t *file_recovery)
{
  int hash;
  int idx;
  int i;
  uint64_t max_filesize;
  int chain_length = 0; // Track collision chain length

  // Safety check
  if (!file_recovery)
  {
    return -1;
  }

  init_buffer_hash_table();

  hash = hash_file_recovery(file_recovery);
  idx = hash_table[hash];

  // Search collision chain for existing buffer
  while (idx != -1)
  {
    chain_length++;
    if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery)
    {
      return idx;
    }
    idx = file_buffers[idx].next_index;
  }

  // Update collision statistics (disabled for performance)
  // if (chain_length > 0) {
  //     buffer_stats.hash_collisions++;
  //     if (chain_length > buffer_stats.max_chain_length) {
  //         buffer_stats.max_chain_length = chain_length;
  //     }
  // }

  // OPTIMIZATION: Get free slot from free list (O(1) instead of O(N))
  if (free_list_head == -1)
  {
    log_critical("BUFFER POOL FULL: Cannot allocate buffer for %s (max=%d)\n",
                 file_recovery->filename, MAX_FILE_BUFFERS);
    return -1; // No free slots
  }

  i = free_list_head;
  free_list_head = file_buffers[i].next_index; // Remove from free list

  // Initialize new buffer slot
  file_buffers[i].file_recovery_ptr = file_recovery;
  file_buffers[i].is_active = 1;

  // Copy filename to buffer for safe access during flush
  strncpy(file_buffers[i].filename, file_recovery->filename, sizeof(file_buffers[i].filename) - 1);
  file_buffers[i].filename[sizeof(file_buffers[i].filename) - 1] = '\0';

  // FIXED: Allocate EXACT buffer size based on filesize filter (no resizing!)
  max_filesize = get_buffer_size_for_file(file_recovery);
  {
    size_t buffer_size = (size_t)max_filesize;

    // Use calloc for safety (zero-initialized memory)
    file_buffers[i].buffer = calloc(1, buffer_size);
    file_buffers[i].buffer_size = 0;
    file_buffers[i].buffer_capacity = buffer_size;
    file_buffers[i].save_handle = NULL; // Initialize save_handle to NULL
    file_buffers[i].next_index = -1;
    file_buffers[i].already_flushed = 0;

    if (!file_buffers[i].buffer)
    {
      log_critical("BUFFER ALLOC FAILED: Cannot allocate %llu bytes for %s\n",
                   (unsigned long long)buffer_size, file_recovery->filename);
      file_buffers[i].is_active = 0; // Mark as inactive on failure
      // OPTIMIZATION: Add back to free list on allocation failure
      file_buffers[i].next_index = free_list_head;
      free_list_head = i;
      return -1;
    }

    // Create read_handle using fopencookie for memory buffer reading
    buffer_cookie_t *cookie = malloc(sizeof(buffer_cookie_t));
    if (!cookie)
    {
      log_critical("COOKIE ALLOC FAILED for %s\n", file_recovery->filename);
      free(file_buffers[i].buffer);
      file_buffers[i].buffer = NULL;
      file_buffers[i].is_active = 0;
      // OPTIMIZATION: Add back to free list on cookie allocation failure
      file_buffers[i].next_index = free_list_head;
      free_list_head = i;
      return -1;
    }

    cookie->buffer_idx = i;
    cookie->position = 0;

    // Define I/O operations for fopencookie
    cookie_io_functions_t io_funcs = {
        .read = buffer_read,
        .write = NULL, // Read-only
        .seek = buffer_seek,
        .close = buffer_close};

    // Create read_handle - opened ONCE for the lifetime of buffer
    file_buffers[i].read_handle = fopencookie(cookie, "rb", io_funcs);
    if (!file_buffers[i].read_handle)
    {
      log_critical("FOPENCOOKIE FAILED for %s\n", file_recovery->filename);
      free(cookie);
      free(file_buffers[i].buffer);
      file_buffers[i].buffer = NULL;
      file_buffers[i].is_active = 0;
      // OPTIMIZATION: Add back to free list on fopencookie failure
      file_buffers[i].next_index = free_list_head;
      free_list_head = i;
      return -1;
    }
  }

  // Update memory usage statistics (disabled for performance)
  // buffer_stats.memory_usage += file_buffers[i].buffer_capacity;

  // Add to hash table (insert at head of collision chain)
  file_buffers[i].next_index = hash_table[hash];
  hash_table[hash] = i;

  return i;
}

// Memory buffer writing - FIXED: No resizing, strict bounds checking
int file_buffer_write(file_recovery_t *file_recovery, const void *data, size_t size)
{
  int idx;

  if (!file_recovery || !data || size == 0)
  {
    return -1;
  }

  idx = get_buffer_index(file_recovery);
  if (idx < 0)
  {
    // FALLBACK: Buffer table full - reject file
    buffer_stats.disk_fallback_full++;
    return -1;
  }

  // FIXED: No resizing - if data doesn't fit, reject the file
  if (file_buffers[idx].buffer_size + size > file_buffers[idx].buffer_capacity)
  {
    // File exceeds buffer capacity - reject it
    buffer_stats.disk_fallback_size++;
    return -1;
  }

  // Add to buffer
  memcpy(file_buffers[idx].buffer + file_buffers[idx].buffer_size, data, size);
  file_buffers[idx].buffer_size += size;

  buffer_stats.buffer_writes++;

  return 0;
}

// Print enhanced buffer statistics as JSON to log file
void print_buffer_statistics(void)
{
  static time_t last_log_time = 0;
  time_t current_time = time(NULL);

  // Log every 5 seconds
  if (current_time - last_log_time < 5)
  {
    return;
  }
  last_log_time = current_time;

  unsigned long total_writes = buffer_stats.buffer_writes +
                               buffer_stats.disk_fallback_full +
                               buffer_stats.disk_fallback_size +
                               buffer_stats.disk_fallback_oom;

  // DISABLED: Buffer statistics logging to reduce I/O
  /*
  if (total_writes > 0) {
      FILE *log_file = fopen("/home/piotr/buffer_stats.json", "a");
      if (log_file) {
          fprintf(log_file,
              "{\"timestamp\":%ld,"
              "\"buffer_writes\":%lu,"
              "\"disk_fallback_full\":%lu,"
              "\"disk_fallback_size\":%lu,"
              "\"disk_fallback_oom\":%lu,"
              "\"hash_collisions\":%lu,"
              "\"max_chain_length\":%lu,"
              "\"memory_usage\":%lu,"
              "\"realloc_count\":%lu,"
              "\"total_writes\":%lu,"
              "\"buffer_rate\":%.1f}\n",
              current_time,
              buffer_stats.buffer_writes,
              buffer_stats.disk_fallback_full,
              buffer_stats.disk_fallback_size,
              buffer_stats.disk_fallback_oom,
              buffer_stats.hash_collisions,
              buffer_stats.max_chain_length,
              buffer_stats.memory_usage,
              buffer_stats.realloc_count,
              total_writes,
              (buffer_stats.buffer_writes * 100.0) / total_writes);
          fclose(log_file);
      }
  }
  */
}

// Get buffer data for file_check functions to work on memory instead of disk
const unsigned char *file_buffer_get_data(file_recovery_t *file_recovery, size_t *buffer_size)
{
  if (!file_recovery || !buffer_size)
  {
    return NULL;
  }

  init_buffer_hash_table();

  int hash = hash_file_recovery(file_recovery);
  int idx = hash_table[hash];

  // Search collision chain
  while (idx != -1)
  {
    if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery)
    {
      *buffer_size = file_buffers[idx].buffer_size;
      return (const unsigned char *)file_buffers[idx].buffer;
    }
    idx = file_buffers[idx].next_index;
  }

  *buffer_size = 0;
  return NULL;
}

// Returns 1 if file is in memory buffer (skip disk-based file_check)
// Returns 0 if file should use normal disk-based file_check
int read_file_data_from_buffer(file_recovery_t *file_recovery)
{
  if (!file_recovery)
    return 0;

  size_t buffer_size;
  const unsigned char *buffer_data = file_buffer_get_data(file_recovery, &buffer_size);

  if (buffer_data && buffer_size > 0)
  {
    // Store buffer data in file_recovery struct for file_check functions
    file_recovery->memory_buffer = (unsigned char *)buffer_data;
    file_recovery->buffer_size = buffer_size;

    // Return 1 to indicate file_check should skip (data is in memory)
    return 1;
  }

  // File not in buffer or traditional mode - use normal disk-based file_check
  return 0;
}

// IMPROVED: Better error handling and memory leak prevention
int file_buffer_clear(file_recovery_t *file_recovery)
{
  int hash;
  int idx, prev_idx;

  if (!file_recovery)
    return 0;

  init_buffer_hash_table();
  hash = hash_file_recovery(file_recovery);
  idx = hash_table[hash];
  prev_idx = -1;

  // Search collision chain
  while (idx != -1)
  {
    if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery)
    {
      // Close read handle if open (this will call buffer_close and free cookie)
      if (file_buffers[idx].read_handle)
      {
        fclose(file_buffers[idx].read_handle);
        file_buffers[idx].read_handle = NULL;
      }

      // Close save handle if open
      if (file_buffers[idx].save_handle)
      {
        fclose(file_buffers[idx].save_handle);
        file_buffers[idx].save_handle = NULL;
      }

      // Update memory usage statistics before freeing
      if (file_buffers[idx].buffer)
      {
        // buffer_stats.memory_usage -= file_buffers[idx].buffer_capacity;
        free(file_buffers[idx].buffer);
        file_buffers[idx].buffer = NULL;
      }

      // Remove from collision chain to prevent infinite loops
      if (prev_idx == -1)
      {
        // It's the head of the chain
        hash_table[hash] = file_buffers[idx].next_index;
      }
      else
      {
        // It's in the middle/end of chain
        file_buffers[prev_idx].next_index = file_buffers[idx].next_index;
      }

      // Mark as inactive
      file_buffers[idx].is_active = 0;
      file_buffers[idx].file_recovery_ptr = NULL;
      file_buffers[idx].buffer_size = 0;
      file_buffers[idx].buffer_capacity = 0;
      file_buffers[idx].already_flushed = 0;

      // OPTIMIZATION: Add back to free list
      file_buffers[idx].next_index = free_list_head;
      free_list_head = idx;

      return 0;
    }
    prev_idx = idx;
    idx = file_buffers[idx].next_index;
  }
  return 0; // Buffer not found, already cleared
}

// Create file handle for buffer if needed
static FILE* create_buffer_save_handle(int buffer_idx)
{
  if (buffer_idx < 0 || buffer_idx >= MAX_FILE_BUFFERS)
  {
    return NULL;
  }

  if (!file_buffers[buffer_idx].is_active)
  {
    return NULL;
  }

  // Return existing handle if already created
  if (file_buffers[buffer_idx].save_handle)
  {
    return file_buffers[buffer_idx].save_handle;
  }

  // Create new file handle
  file_buffers[buffer_idx].save_handle = fopen(file_buffers[buffer_idx].filename, "w+b");

  if (!file_buffers[buffer_idx].save_handle)
  {
    log_critical("Cannot create file %s for buffer: %s\n",
                 file_buffers[buffer_idx].filename, strerror(errno));
  }

  return file_buffers[buffer_idx].save_handle;
}

// IMPROVED: Better error handling and memory leak prevention
int file_buffer_flush(file_recovery_t *file_recovery)
{
  int hash;
  int idx, prev_idx;

  if (!file_recovery)
    return 0;

  init_buffer_hash_table();
  hash = hash_file_recovery(file_recovery);
  idx = hash_table[hash];
  prev_idx = -1;

  // Search collision chain
  while (idx != -1)
  {
    if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery)
    {
      // NOTE: Filesize filtering is done in file_finish_bf/file_finish2 BEFORE flush
      // This function just writes the buffer to disk

      // Create file handle if needed and write buffer to disk
      if (file_buffers[idx].buffer_size > 0 && !file_buffers[idx].already_flushed)
      {
        // Create file handle using helper function
        FILE *handle = create_buffer_save_handle(idx);
        if (!handle)
        {
          // IMPROVED: Clean up memory even on error
          if (file_buffers[idx].buffer)
          {
            // buffer_stats.memory_usage -= file_buffers[idx].buffer_capacity;
            free(file_buffers[idx].buffer);
            file_buffers[idx].buffer = NULL;
          }
          file_buffers[idx].is_active = 0;
          return -1;
        }

        if (fwrite(file_buffers[idx].buffer, 1, file_buffers[idx].buffer_size,
                   handle) != file_buffers[idx].buffer_size)
        {
          // IMPROVED: Clean up memory even on write error
          if (file_buffers[idx].buffer)
          {
            // buffer_stats.memory_usage -= file_buffers[idx].buffer_capacity;
            free(file_buffers[idx].buffer);
            file_buffers[idx].buffer = NULL;
          }
          if (file_buffers[idx].save_handle)
          {
            fclose(file_buffers[idx].save_handle);
            file_buffers[idx].save_handle = NULL;
          }
          file_buffers[idx].is_active = 0;
          return -1;
        }

        // Close save_handle after successful write
        if (file_buffers[idx].save_handle)
        {
          fclose(file_buffers[idx].save_handle);
          file_buffers[idx].save_handle = NULL;
        }

        // Copy handle to file_recovery for compatibility (open for reading)
        if (file_recovery->handle == NULL)
        {
          file_recovery->handle = fopen(file_buffers[idx].filename, "r+b");
        }
      }

      // Free memory and update statistics
      if (file_buffers[idx].buffer)
      {
        // buffer_stats.memory_usage -= file_buffers[idx].buffer_capacity;
        free(file_buffers[idx].buffer);
        file_buffers[idx].buffer = NULL;
      }

      // Remove from collision chain to prevent infinite loops
      if (prev_idx == -1)
      {
        // It's the head of the chain
        hash_table[hash] = file_buffers[idx].next_index;
      }
      else
      {
        // It's in the middle/end of chain
        file_buffers[prev_idx].next_index = file_buffers[idx].next_index;
      }

      // Mark as inactive
      file_buffers[idx].is_active = 0;
      file_buffers[idx].file_recovery_ptr = NULL;
      file_buffers[idx].buffer_size = 0;
      file_buffers[idx].buffer_capacity = 0;
      file_buffers[idx].already_flushed = 0;

      // OPTIMIZATION: Add back to free list
      file_buffers[idx].next_index = free_list_head;
      free_list_head = idx;

      return 0;
    }
    prev_idx = idx;
    idx = file_buffers[idx].next_index;
  }
  return 0; // Buffer not found
}

// Flush all active buffers - called at program exit
void flush_all_buffers(void)
{
  int flushed_count = 0;
  int error_count = 0;

  for (int i = 0; i < MAX_FILE_BUFFERS; i++)
  {
    if (file_buffers[i].is_active && !file_buffers[i].already_flushed)
    {
      if (file_buffer_flush(file_buffers[i].file_recovery_ptr) == 0)
      {
        flushed_count++;
      }
      else
      {
        error_count++;
      }
    }
  }

  if (flushed_count > 0)
  {
    // log_info("Final flush: %d buffers flushed successfully", flushed_count);
    if (error_count > 0)
    {
      log_warning("Final flush: %d buffers had errors", error_count);
    }
  }
}

// Set global file size filter for all recovery operations
void set_global_file_size_filter(const file_size_filter_t *filter)
{
  if (filter != NULL)
  {
    global_file_size_filter = *filter; // Copy values, not pointer!
    log_info("FILTER: Global filesize filter set: min=%llu, max=%llu\n",
             (unsigned long long)filter->min_file_size,
             (unsigned long long)filter->max_file_size);
  }
  else
  {
    global_file_size_filter.min_file_size = 0;
    global_file_size_filter.max_file_size = 0;
    log_info("FILTER: Global filesize filter cleared\n");
  }
}

// Get user's max limit (0 = no limit)
uint64_t get_user_max_filesize(void)
{
  return global_file_size_filter.max_file_size;
}

// Get user's min limit (0 = no limit)
uint64_t get_user_min_filesize(void)
{
  return global_file_size_filter.min_file_size;
}

// Get read handle from buffer - returns fopencookie handle for reading buffer data
// This handle automatically tracks buffer_size for EOF
FILE *get_buffer_read_handle(file_recovery_t *file_recovery)
{
  if (!file_recovery)
  {
    return NULL;
  }

  init_buffer_hash_table();

  int hash = hash_file_recovery(file_recovery);
  int idx = hash_table[hash];

  // Search collision chain
  while (idx != -1)
  {
    if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery)
    {
      if (file_buffers[idx].read_handle)
      {
        // Reset position to beginning for fresh read
        fseek(file_buffers[idx].read_handle, 0, SEEK_SET);
        return file_buffers[idx].read_handle;
      }
      return NULL;
    }
    idx = file_buffers[idx].next_index;
  }

  return NULL;
}