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

// Enhanced statistics for monitoring buffer vs disk usage
static struct {
    unsigned long buffer_writes;      // Successful buffer writes
    unsigned long disk_fallback_full; // Fallback due to buffer pool full
    unsigned long disk_fallback_size; // Fallback due to file too large
    unsigned long disk_fallback_oom;  // Fallback due to malloc/realloc failure
    unsigned long hash_collisions;    // NEW: Hash collision count
    unsigned long max_chain_length;   // NEW: Longest collision chain
    unsigned long memory_usage;       // NEW: Current memory usage
    unsigned long realloc_count;      // NEW: Number of buffer reallocations
} buffer_stats = {0, 0, 0, 0, 0, 0, 0, 0};

static struct {
    file_recovery_t *file_recovery_ptr;  // Use file_recovery pointer as stable key
    char filename[2048];                 // Store filename copy to avoid segfaults
    unsigned char *buffer;
    size_t buffer_size;
    size_t buffer_capacity;
    int next_index; // For collision chaining, -1 means end of chain
    int already_flushed;  // Flag to prevent double-writing
    int is_active;      // Mark if buffer slot is active (1) or free (0)
} file_buffers[MAX_FILE_BUFFERS];

static int hash_table[HASH_TABLE_SIZE]; // Index into file_buffers, -1 means empty

// Global file size filter for all recovery operations (copy, not pointer!)
static file_size_filter_t global_file_size_filter = {0, 0};

// Fast simple hash function for performance
static int hash_file_recovery(file_recovery_t *file_recovery) {
    uintptr_t ptr = (uintptr_t)file_recovery;
    uint32_t high = (uint32_t)(ptr >> 32);
    uint32_t low = (uint32_t)(ptr & 0xFFFFFFFF);
    unsigned int hash = high ^ low;
    return hash % HASH_TABLE_SIZE;
}

// Initialize hash table (call once at startup)
static void init_buffer_hash_table(void) {
    static int initialized = 0;
    if (!initialized) {
        for (int i = 0; i < HASH_TABLE_SIZE; i++) {
            hash_table[i] = -1;
        }
        for (int i = 0; i < MAX_FILE_BUFFERS; i++) {
            file_buffers[i].next_index = -1;
            file_buffers[i].is_active = 0;
            file_buffers[i].file_recovery_ptr = NULL;
            file_buffers[i].filename[0] = '\0';
            file_buffers[i].buffer = NULL;  // IMPORTANT: Initialize to NULL
            file_buffers[i].buffer_size = 0;
            file_buffers[i].buffer_capacity = 0;
            file_buffers[i].already_flushed = 0;
        }
        initialized = 1;
    }
}

// Get max file size for this file type (respects user limits)
static uint64_t get_max_filesize_for_buffer(file_recovery_t *file_recovery)
{
  // Start with file type's limit
  uint64_t type_max = PHOTOREC_MAX_FILE_SIZE; // Global default
  uint64_t user_max;

  if(file_recovery->file_stat && file_recovery->file_stat->file_hint &&
     file_recovery->file_stat->file_hint->max_filesize > 0) {
    type_max = file_recovery->file_stat->file_hint->max_filesize;
  }

  // If user has max limit, use the smaller of the two
  user_max = get_user_max_filesize();
  if (user_max > 0 && user_max < type_max) {
    return user_max;
  }

  return type_max;
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
    int chain_length = 0;  // Track collision chain length

    // Safety check
    if (!file_recovery) {
        return -1;
    }

    init_buffer_hash_table();

    hash = hash_file_recovery(file_recovery);
    idx = hash_table[hash];

    // Search collision chain for existing buffer
    while (idx != -1) {
        chain_length++;
        if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery) {
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

    // Find free slot in buffer array
    for (i = 0; i < MAX_FILE_BUFFERS; i++) {
        if (!file_buffers[i].is_active) {
            break;
        }
    }

    if (i >= MAX_FILE_BUFFERS) {
        return -1; // No free slots
    }

    // Initialize new buffer slot
    file_buffers[i].file_recovery_ptr = file_recovery;
    file_buffers[i].is_active = 1;

    // Copy filename to buffer for safe access during flush
    strncpy(file_buffers[i].filename, file_recovery->filename, sizeof(file_buffers[i].filename) - 1);
    file_buffers[i].filename[sizeof(file_buffers[i].filename) - 1] = '\0';

    // Smart initial allocation based on file type
    max_filesize = get_max_filesize_for_buffer(file_recovery);
    {
        size_t initial_size = (max_filesize > 1024*1024) ? 1024*1024 : (size_t)max_filesize; // Start with 1MB or file max, whichever is smaller

        // Use calloc for safety (zero-initialized memory)
        file_buffers[i].buffer = calloc(1, initial_size);
        file_buffers[i].buffer_size = 0;
        file_buffers[i].buffer_capacity = initial_size;
        file_buffers[i].next_index = -1;
        file_buffers[i].already_flushed = 0;
    }

    if (!file_buffers[i].buffer) {
        file_buffers[i].is_active = 0;  // Mark as inactive on failure
        return -1;
    }

    // Update memory usage statistics (disabled for performance)
    // buffer_stats.memory_usage += file_buffers[i].buffer_capacity;

    // Add to hash table (insert at head of collision chain)
    file_buffers[i].next_index = hash_table[hash];
    hash_table[hash] = i;

    return i;
}

// Memory buffer writing with improved error handling
int file_buffer_write(file_recovery_t *file_recovery, const void *data, size_t size)
{
    int idx;
    uint64_t max_filesize;

    if (!file_recovery || !data || size == 0) {
        return -1;
    }

    // PERFORMANCE: Quick fallback to disk for large files without user filters
    if (!has_user_filesize_limits() && size > 1024*1024) {
        // Large file without filters - write directly to disk
        if (!file_recovery->handle) return -1;
        return (fwrite(data, 1, size, file_recovery->handle) == size) ? 0 : -1;
    }

    idx = get_buffer_index(file_recovery);
    if (idx < 0) {
        // FALLBACK: Buffer table full - writing to disk
        buffer_stats.disk_fallback_full++;
        log_info("FALLBACK: Buffer table full for %s - writing to disk", file_recovery->filename);
        if (!file_recovery->handle) return -1;
        return (fwrite(data, 1, size, file_recovery->handle) == size) ? 0 : -1;
    }

    // Check if we exceed max file size for this file type (fallback behavior when no user limits)
    max_filesize = get_max_filesize_for_buffer(file_recovery);
    if (file_buffers[idx].buffer_size + size > max_filesize) {
        // FALLBACK: File too large for buffer - writing to disk
        buffer_stats.disk_fallback_size++;
        log_info("FALLBACK: File %s too large (%llu bytes) - writing to disk",
                 file_recovery->filename, (unsigned long long)(file_buffers[idx].buffer_size + size));
        if (!has_user_filesize_limits()) {
            if (!file_recovery->handle) return -1;
            return (fwrite(data, 1, size, file_recovery->handle) == size) ? 0 : -1;
        } else {
            return 0; // Skip writing when user has size limits
        }
    }

    // IMPROVED: Better bounds checking before realloc
    if (file_buffers[idx].buffer_size + size > file_buffers[idx].buffer_capacity) {
        // Instead of doubling, grow by chunks but respect max_filesize
        size_t chunk_size = (max_filesize > 10*1024*1024) ? 1024*1024 : max_filesize/4; // 1MB or 25% of max
        size_t needed = file_buffers[idx].buffer_size + size;
        size_t new_capacity = ((needed + chunk_size - 1) / chunk_size) * chunk_size; // Round up to chunk boundary

        // Cap at max_filesize
        if (new_capacity > max_filesize) {
            new_capacity = max_filesize;
        }

        // IMPROVED: Check if realloc is actually needed
        if (new_capacity <= file_buffers[idx].buffer_capacity) {
            log_critical("Buffer capacity insufficient for file %s", file_recovery->filename);
            return -1;
        }

        unsigned char *new_buffer = realloc(file_buffers[idx].buffer, new_capacity);
        if (!new_buffer) {
            // FALLBACK: Out of memory - writing to disk
            buffer_stats.disk_fallback_oom++;
            log_info("FALLBACK: Out of memory for %s (tried %zu bytes) - writing to disk",
                     file_recovery->filename, new_capacity);
            if (!file_recovery->handle) return -1;
            return (fwrite(data, 1, size, file_recovery->handle) == size) ? 0 : -1;
        }

        // Update memory usage statistics (disabled for performance)
        // buffer_stats.memory_usage += new_capacity - file_buffers[idx].buffer_capacity;
        // buffer_stats.realloc_count++;

        file_buffers[idx].buffer = new_buffer;
        file_buffers[idx].buffer_capacity = new_capacity;
    }

    // IMPROVED: Double-check bounds before memcpy
    if (file_buffers[idx].buffer_size + size > file_buffers[idx].buffer_capacity) {
        log_critical("Buffer overflow prevented for file %s", file_recovery->filename);
        return -1;
    }

    // Add to buffer
    memcpy(file_buffers[idx].buffer + file_buffers[idx].buffer_size, data, size);
    file_buffers[idx].buffer_size += size;

    buffer_stats.buffer_writes++;

    // Log stats periodically (disabled for performance)
    // print_buffer_statistics();

    return 0;
}

// Print enhanced buffer statistics as JSON to log file
void print_buffer_statistics(void)
{
    static time_t last_log_time = 0;
    time_t current_time = time(NULL);

    // Log every 5 seconds
    if (current_time - last_log_time < 5) {
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
const unsigned char* file_buffer_get_data(file_recovery_t *file_recovery, size_t *buffer_size)
{
    if (!file_recovery || !buffer_size) {
        return NULL;
    }

    init_buffer_hash_table();

    int hash = hash_file_recovery(file_recovery);
    int idx = hash_table[hash];

    // Search collision chain
    while (idx != -1) {
        if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery) {
            *buffer_size = file_buffers[idx].buffer_size;
            return (const unsigned char*)file_buffers[idx].buffer;
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
  if (!file_recovery) return 0;

  // If using memory buffering, check if we have data in buffer
  if (file_recovery->use_memory_buffering) {
    size_t buffer_size;
    const unsigned char *buffer_data = file_buffer_get_data(file_recovery, &buffer_size);

    if (buffer_data && buffer_size > 0) {
      // Store buffer data in file_recovery struct for file_check functions
      file_recovery->memory_buffer = (unsigned char*)buffer_data;
      file_recovery->buffer_size = buffer_size;

      // Return 1 to indicate file_check should skip (data is in memory)
      return 1;
    }
  }

  // File not in buffer or traditional mode - use normal disk-based file_check
  return 0;
}

// IMPROVED: Better error handling and memory leak prevention
int file_buffer_clear(file_recovery_t *file_recovery)
{
    int hash;
    int idx, prev_idx;

    if (!file_recovery) return 0;

    init_buffer_hash_table();
    hash = hash_file_recovery(file_recovery);
    idx = hash_table[hash];
    prev_idx = -1;

    // Search collision chain
    while (idx != -1) {
        if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery) {
            // Update memory usage statistics before freeing
            if (file_buffers[idx].buffer) {
                // buffer_stats.memory_usage -= file_buffers[idx].buffer_capacity;
                free(file_buffers[idx].buffer);
                file_buffers[idx].buffer = NULL;
            }

            // Remove from collision chain to prevent infinite loops
            if (prev_idx == -1) {
                // It's the head of the chain
                hash_table[hash] = file_buffers[idx].next_index;
            } else {
                // It's in the middle/end of chain
                file_buffers[prev_idx].next_index = file_buffers[idx].next_index;
            }

            // Mark as inactive
            file_buffers[idx].is_active = 0;
            file_buffers[idx].file_recovery_ptr = NULL;
            file_buffers[idx].buffer_size = 0;
            file_buffers[idx].buffer_capacity = 0;
            file_buffers[idx].already_flushed = 0;
            file_buffers[idx].next_index = -1;

            return 0;
        }
        prev_idx = idx;
        idx = file_buffers[idx].next_index;
    }
    return 0; // Buffer not found, already cleared
}

// IMPROVED: Better error handling and memory leak prevention
int file_buffer_flush(file_recovery_t *file_recovery)
{
    int hash;
    int idx, prev_idx;

    if (!file_recovery) return 0;

    init_buffer_hash_table();
    hash = hash_file_recovery(file_recovery);
    idx = hash_table[hash];
    prev_idx = -1;

    // Search collision chain
    while (idx != -1) {
        if (file_buffers[idx].is_active && file_buffers[idx].file_recovery_ptr == file_recovery) {
            // Create file handle if needed and write buffer to disk
            if (file_buffers[idx].buffer_size > 0 && !file_buffers[idx].already_flushed) {
                // Create file handle if it doesn't exist
                if (!file_recovery->handle) {
                    file_recovery->handle = fopen(file_recovery->filename, "w+b");
                    if (!file_recovery->handle) {
                        log_critical("Cannot create file %s during flush: %s\n",
                                   file_recovery->filename, strerror(errno));
                        // IMPROVED: Clean up memory even on error
                        if (file_buffers[idx].buffer) {
                            // buffer_stats.memory_usage -= file_buffers[idx].buffer_capacity;
                            free(file_buffers[idx].buffer);
                            file_buffers[idx].buffer = NULL;
                        }
                        file_buffers[idx].is_active = 0;
                        return -1;
                    }
                }

                if (fwrite(file_buffers[idx].buffer, 1, file_buffers[idx].buffer_size,
                          file_recovery->handle) != file_buffers[idx].buffer_size) {
                    // IMPROVED: Clean up memory even on write error
                    if (file_buffers[idx].buffer) {
                        // buffer_stats.memory_usage -= file_buffers[idx].buffer_capacity;
                        free(file_buffers[idx].buffer);
                        file_buffers[idx].buffer = NULL;
                    }
                    file_buffers[idx].is_active = 0;
                    return -1;
                }
            }

            // Free memory and update statistics
            if (file_buffers[idx].buffer) {
                // buffer_stats.memory_usage -= file_buffers[idx].buffer_capacity;
                free(file_buffers[idx].buffer);
                file_buffers[idx].buffer = NULL;
            }

            // Remove from collision chain to prevent infinite loops
            if (prev_idx == -1) {
                // It's the head of the chain
                hash_table[hash] = file_buffers[idx].next_index;
            } else {
                // It's in the middle/end of chain
                file_buffers[prev_idx].next_index = file_buffers[idx].next_index;
            }

            // Mark as inactive
            file_buffers[idx].is_active = 0;
            file_buffers[idx].file_recovery_ptr = NULL;
            file_buffers[idx].buffer_size = 0;
            file_buffers[idx].buffer_capacity = 0;
            file_buffers[idx].already_flushed = 0;
            file_buffers[idx].next_index = -1;

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

    for (int i = 0; i < MAX_FILE_BUFFERS; i++) {
        if (file_buffers[i].is_active && !file_buffers[i].already_flushed) {
            if (file_buffer_flush(file_buffers[i].file_recovery_ptr) == 0) {
                flushed_count++;
            } else {
                error_count++;
            }
        }
    }

    if (flushed_count > 0) {
        // log_info("Final flush: %d buffers flushed successfully", flushed_count);
        if (error_count > 0) {
            log_warning("Final flush: %d buffers had errors", error_count);
        }
    }
}

// Set global file size filter for all recovery operations
void set_global_file_size_filter(const file_size_filter_t *filter)
{
  if (filter != NULL) {
    global_file_size_filter = *filter; // Copy values, not pointer!
  } else {
    global_file_size_filter.min_file_size = 0;
    global_file_size_filter.max_file_size = 0;
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