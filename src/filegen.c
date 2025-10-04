/*

    File: filegen.c

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

#ifdef DISABLED_FOR_FRAMAC
#undef HAVE_FTELLO
#undef HAVE_FSEEKO
#endif

#ifdef HAVE_STDLIB_H
#include <stdlib.h>
#endif
#ifdef HAVE_STRING_H
#include <string.h>
#endif
#include <stdio.h>
#include <ctype.h>
#include <errno.h>
#include <assert.h>
#ifdef HAVE_TIME_H
#include <time.h>
#endif
#include "types.h"
#include "common.h"
#include "filegen.h"
#include "photorec.h"
#include "log.h"

static int file_check_cmp(const struct td_list_head *a, const struct td_list_head *b);

#ifndef __FRAMAC__
#include "list_add_sorted.h"
#else

/*@
  @ requires \valid(newe);
  @ requires \valid(head);
  @ requires separation: \separated(newe, head);
  @ requires list_separated(head->prev, newe);
  @ requires list_separated(head, newe);
  @ requires finite(head->prev);
  @ requires finite(head);
  @*/
static inline void td_list_add_sorted_fcc(struct td_list_head *newe, struct td_list_head *head)
{
  struct td_list_head *pos;
  /*@
    @ loop invariant \valid(pos);
    @ loop invariant \valid(pos->prev);
    @ loop invariant \valid(pos->next);
    @ loop invariant pos == head || \separated(pos, head);
    @ loop invariant finite(head);
    @ loop assigns pos;
    @*/
  td_list_for_each(pos, head)
  {
    /*@ assert \valid_read(newe); */
    /*@ assert \valid_read(pos); */
    if(file_check_cmp(newe,pos)<0)
      break;
  }
  if(pos != head)
  {
      __td_list_add(newe, pos->prev, pos);
  }
  else
  {
    /*@ assert finite(head->prev); */
    /*@ assert finite(head); */
    /*@ assert list_separated(head->prev, newe); */
    /*@ assert list_separated(head, newe); */
    td_list_add_tail(newe, head);
  }
}
#endif


uint64_t gpls_nbr=0;
static uint64_t offset_skipped_header=0;

static  file_check_t file_check_plist={
  .list = TD_LIST_HEAD_INIT(file_check_plist.list)
};

file_check_list_t file_check_list={
    .list = TD_LIST_HEAD_INIT(file_check_list.list)
};

/*@
  @ requires \valid_read(a);
  @ requires \valid_read(b);
  @ assigns \nothing;
  @*/
static int file_check_cmp(const struct td_list_head *a, const struct td_list_head *b)
{
#ifdef DISABLED_FOR_FRAMAC
  return 1;
#else
  const file_check_t *fc_a=td_list_entry_const(a, const file_check_t, list);
  const file_check_t *fc_b=td_list_entry_const(b, const file_check_t, list);
  /*@ requires valid_file_check_node(fc_a); */
  /*@ requires valid_file_check_node(fc_b); */
  int res;
  unsigned int min_length;
  /*@ assert \valid_read(fc_a); */
  /*@ assert \valid_read(fc_b); */
  /*@ assert fc_a->length==0 ==> fc_a->offset == 0; */
  /*@ assert fc_b->length==0 ==> fc_b->offset == 0; */
  if(fc_a->length==0 && fc_b->length!=0)
    return -1;
  if(fc_a->length!=0 && fc_b->length==0)
    return 1;
  /*@ assert (fc_a->length > 0 && fc_b->length > 0) || (fc_a->length == 0 && fc_b->length == 0) ; */
  res=(int)fc_a->offset-(int)fc_b->offset;
  if(res!=0)
    return res;
  /*@ assert fc_a->offset == fc_b->offset; */
  if(fc_a->length==0 && fc_b->length==0)
    return 0;
  /*@ assert fc_a->length > 0 && fc_b->length > 0; */
  /*@ assert \valid_read((char *)fc_a->value + (0 .. fc_a->length - 1)); */
  /*@ assert \valid_read((char *)fc_b->value + (0 .. fc_b->length - 1)); */
  /*@ assert \initialized((char *)fc_a->value + (0 .. fc_a->length - 1)); */
  /*@ assert \initialized((char *)fc_b->value + (0 .. fc_b->length - 1)); */
  min_length=fc_a->length<=fc_b->length?fc_a->length:fc_b->length;
  res=memcmp(fc_a->value,fc_b->value, min_length);
  if(res!=0)
    return res;
  return (int)fc_b->length-(int)fc_a->length;
#endif
}

/*@
  @ requires \valid(file_check_new);
  @ requires \valid(pos);
  @ requires initialization: \initialized(&file_check_new->offset) && \initialized(&file_check_new->length);
  @ requires valid_file_check_node(file_check_new);
  @*/
static void file_check_add_tail(file_check_t *file_check_new, file_check_list_t *pos)
{
  unsigned int i;
  const unsigned int tmp=(file_check_new->length==0?0:((const unsigned char *)file_check_new->value)[0]);
  file_check_list_t *newe=(file_check_list_t *)MALLOC(sizeof(*newe));
  /*@ assert \valid(newe); */
  newe->offset=file_check_new->offset;
  /*@
    @ loop unroll 256;
    @ loop invariant 0 <= i <= 256;
    @ loop invariant \forall integer j; (0 <= j < i) ==> newe->file_checks[j].list.prev == &newe->file_checks[j].list;
    @ loop invariant \forall integer j; (0 <= j < i) ==> newe->file_checks[j].list.next == &newe->file_checks[j].list;
    @ loop assigns i, newe->file_checks[0 .. i-1].list.prev, newe->file_checks[0 .. i-1].list.next;
    @ loop variant 255-i;
    @*/
  for(i=0;i<256;i++)
  {
    TD_INIT_LIST_HEAD(&newe->file_checks[i].list);
    /*@ assert newe->file_checks[i].list.prev == &newe->file_checks[i].list; */
    /*@ assert newe->file_checks[i].list.next == &newe->file_checks[i].list; */
  }
  /*@ assert 0 <= tmp <= 255; */
  /*@ assert newe->file_checks[tmp].list.prev == &newe->file_checks[tmp].list; */
  /*@ assert newe->file_checks[tmp].list.next == &newe->file_checks[tmp].list; */
  td_list_add_tail(&file_check_new->list, &newe->file_checks[tmp].list);
  td_list_add_tail(&newe->list, &pos->list);
}

#ifndef DISABLED_FOR_FRAMAC
/*@
  @ requires separation: \separated(file_stat, &file_check_plist);
  @*/
#endif
void register_header_check(const unsigned int offset, const void *value, const unsigned int length,
    int (*header_check)(const unsigned char *buffer, const unsigned int buffer_size,
      const unsigned int safe_header_only, const file_recovery_t *file_recovery, file_recovery_t *file_recovery_new),
    file_stat_t *file_stat)
{
  file_check_t *file_check_new=(file_check_t *)MALLOC(sizeof(*file_check_new));
  /*@ assert \valid(file_check_new); */
  file_check_new->value=value;
  file_check_new->length=length;
  file_check_new->offset=offset;
  /*@ assert header_check != \null; */
  file_check_new->header_check=header_check;
  /*@ assert file_check_new->header_check != \null; */
  file_check_new->file_stat=file_stat;

  /*@ assert \valid_read(file_check_new); */
  /*@ assert \initialized(&file_check_new->offset); */
  /*@ assert \initialized(&file_check_new->length); */
  /*@ assert file_check_new->offset <= PHOTOREC_MAX_SIG_OFFSET; */
  /*@ assert 0 < file_check_new->length <= PHOTOREC_MAX_SIG_SIZE; */
  /*@ assert file_check_new->offset + file_check_new->length <= PHOTOREC_MAX_SIG_OFFSET; */
  /*@ assert \valid_read((const char *)file_check_new->value+(0..file_check_new->length-1)); */
  /*@ assert \valid_function(file_check_new->header_check); */
  /*@ assert \valid(file_check_new->file_stat); */

  /*@ assert valid_file_check_node(file_check_new); */
#ifdef __FRAMAC__
  td_list_add_sorted_fcc(&file_check_new->list, &file_check_plist.list);
#else
  td_list_add_sorted(&file_check_new->list, &file_check_plist.list, file_check_cmp);
#endif
}

/*@
  @ requires \valid(file_check_new);
  @ requires valid_file_check_node(file_check_new);
  @*/
static void index_header_check_aux(file_check_t *file_check_new)
{
  /* file_check_list is sorted by increasing offset */
  if(file_check_new->length>0)
  {
    /*@ assert file_check_new->offset < 0x80000000; */
    /*@ assert 0 < file_check_new->length <= 4096; */
    struct td_list_head *tmp;
    /*@
      @ loop invariant \valid(tmp);
      @*/
    td_list_for_each(tmp, &file_check_list.list)
    {
      file_check_list_t *pos=td_list_entry(tmp, file_check_list_t, list);
      if(pos->offset >= file_check_new->offset &&
	  pos->offset < file_check_new->offset+file_check_new->length)
      {
#ifdef __FRAMAC__
	td_list_add_sorted_fcc(&file_check_new->list,
	    &pos->file_checks[((const unsigned char *)file_check_new->value)[pos->offset-file_check_new->offset]].list);
#else
	td_list_add_sorted(&file_check_new->list,
	    &pos->file_checks[((const unsigned char *)file_check_new->value)[pos->offset-file_check_new->offset]].list,
	    file_check_cmp);
#endif
	return ;
      }
      if(pos->offset>file_check_new->offset)
      {
	file_check_add_tail(file_check_new, pos);
	return ;
      }
    }
  }
  file_check_add_tail(file_check_new, &file_check_list);
}

static unsigned int index_header_check(void)
{
  struct td_list_head *tmp;
  struct td_list_head *next;
  unsigned int nbr=0;
  /* Initialize file_check_list from file_check_plist */
  /*@
    @ loop invariant \valid_read(tmp);
    @ loop invariant \valid_read(next);
    @*/
  td_list_for_each_prev_safe(tmp, next, &file_check_plist.list)
  {
    file_check_t *current_check;
    current_check=td_list_entry(tmp, file_check_t, list);
    /*@ assert valid_file_check_node(current_check); */
    /* dettach current_check from file_check_plist */
    td_list_del(tmp);
    /*@ assert \initialized(&current_check->offset) && \initialized(&current_check->length); */
    index_header_check_aux(current_check);
    nbr++;
  }
  return nbr;
}

void free_header_check(void)
{
#ifndef DISABLED_FOR_FRAMAC
  struct td_list_head *tmpl;
  struct td_list_head *nextl;
  td_list_for_each_safe(tmpl, nextl, &file_check_list.list)
  {
    unsigned int i;
    file_check_list_t *pos=td_list_entry(tmpl, file_check_list_t, list);
    /*@
      @ loop unroll 256;
      @ loop invariant 0 <= i <= 256;
      @*/
    /* TODO loop variant 255-i; */
    for(i=0;i<256;i++)
    {
      struct td_list_head *tmp;
      struct td_list_head *next;
      /* TODO loop invariant \valid(next); */
      td_list_for_each_safe(tmp, next, &pos->file_checks[i].list)
      {
#ifdef DEBUG_HEADER_CHECK
	unsigned int j;
	const unsigned char *data;
#endif
	file_check_t *current_check;
	current_check=td_list_entry(tmp, file_check_t, list);
	/*@ assert valid_file_check_node(current_check); */
#ifdef DEBUG_HEADER_CHECK
	data=(const char *)current_check->value;
	log_info("[%u]=%02x length=%u offset=%u", pos->offset, i, current_check->length, current_check->offset);
	if(current_check->file_stat!=NULL && current_check->file_stat->file_hint!=NULL)
	  log_info(" %s", current_check->file_stat->file_hint->description);
	for(j=0; j<current_check->length; j++)
	  log_info(" %02x", data[j]);
	log_info("\n");
#endif
	td_list_del(tmp);
	free(current_check);
      }
    }
#ifdef DEBUG_HEADER_CHECK
    log_info("\n");
#endif
    td_list_del(tmpl);
    free(pos);
  }
#endif
}

void file_allow_nl(file_recovery_t *file_recovery, const unsigned int nl_mode)
{
  /*@ assert valid_file_recovery(file_recovery); */
  /*@ assert valid_file_check_result(file_recovery); */
  char buffer[4096];
  int taille;
  if(file_recovery->file_size >= 0x8000000000000000-2)
  {
    /*@ assert valid_file_check_result(file_recovery); */
    return ;
  }
  /*@ assert \valid(file_recovery->handle); */
  if(my_fseek(file_recovery->handle, file_recovery->file_size,SEEK_SET)<0)
  {
    /*@ assert \valid(file_recovery->handle); */
    /*@ assert valid_file_recovery(file_recovery); */
    /*@ assert valid_file_check_result(file_recovery); */
    return;
  }
  /*@ assert \separated(file_recovery, buffer+(..)); */
  /*@ assert valid_file_recovery(file_recovery); */
  taille=fread(buffer,1, 4096,file_recovery->handle);
  /*@ assert valid_file_recovery(file_recovery); */
#ifdef __FRAMAC__
  Frama_C_make_unknown(&buffer, 4096);
#endif
  /*@ assert valid_file_recovery(file_recovery); */
  /*@ assert file_recovery->file_size < 0x8000000000000000-2; */
  if(taille > 0 && buffer[0]=='\n' && (nl_mode&NL_BARENL)==NL_BARENL)
    file_recovery->file_size++;
  else if(taille > 1 && buffer[0]=='\r' && buffer[1]=='\n' && (nl_mode&NL_CRLF)==NL_CRLF)
    file_recovery->file_size+=2;
  else if(taille > 0 && buffer[0]=='\r' && (nl_mode&NL_BARECR)==NL_BARECR)
    file_recovery->file_size++;
  /*@ assert file_recovery->file_size < 0x8000000000000000; */
  /*@ assert \valid(file_recovery->handle); */
  /*@ assert valid_file_recovery(file_recovery); */
  /*@ assert valid_file_check_result(file_recovery); */
}

uint64_t file_rsearch(FILE *handle, uint64_t offset, const void*footer, const unsigned int footer_length)
{
  /*
   * 4096+footer_length-1: required size
   * 4096+footer_length: to avoid a Frama-C warning when footer_length==1
   * 8192: maximum size
   * */
  char buffer[8192];
  assert(footer_length < 4096);
  /*@ assert 0 < footer_length < 4096; */
  memset(&buffer[4096],0,footer_length-1);
  /*@
    @ loop invariant 0 <= offset <= \at(offset, Pre);
    @ loop invariant offset < 0x8000000000000000;
    @ loop assigns errno, *handle, Frama_C_entropy_source;
    @ loop assigns offset, buffer[0 .. 8192-1];
    @ loop variant offset;
    @*/
  do
  {
    int i;
    int taille;
    if(offset <= 4096)
      offset=0;
    else if(offset%4096==0)
      offset-=4096;
    else
      offset=offset-(offset%4096);
    /*@ assert offset + 4096 <= 0x8000000000000000; */
    if(my_fseek(handle,offset,SEEK_SET)<0)
      return 0;
    taille=fread(&buffer, 1, 4096, handle);
    if(taille <= 0)
      return 0;
    /*@ assert 0 < taille <= 4096; */
#ifdef __FRAMAC__
    Frama_C_make_unknown(&buffer, 4096);
#endif
    /*@
      @ loop invariant -1 <= i < taille;
      @ loop assigns i;
      @ loop variant i;
      @*/
    for(i=taille-1;i>=0;i--)
    {
      /*@ assert offset + i <= 0x8000000000000000; */
      if(buffer[i]==*(const char *)footer && memcmp(&buffer[i],footer,footer_length)==0)
      {
        return offset + i;
      }
    }
    memcpy(buffer+4096,buffer,footer_length-1);
  } while(offset>0);
  return 0;
}

void file_search_footer(file_recovery_t *file_recovery, const void*footer, const unsigned int footer_length, const unsigned int extra_length)
{
  /*@ assert \valid(file_recovery); */
  if(footer_length==0 || file_recovery->file_size <= extra_length)
    return ;
  file_recovery->file_size=file_rsearch(file_recovery->handle, file_recovery->file_size-extra_length, footer, footer_length);
  /*@ assert 0 < footer_length < 4096; */
  /*@ assert extra_length <= PHOTOREC_MAX_FILE_SIZE; */
  /*@ assert file_recovery->file_size < 0x8000000000000000; */
  if(file_recovery->file_size > 0)
    file_recovery->file_size+= (uint64_t)footer_length + extra_length;
  /*@ assert \valid(file_recovery->handle); */
  /*@ assert valid_file_check_result(file_recovery); */
}

data_check_t data_check_size(const unsigned char *buffer, const unsigned int buffer_size, file_recovery_t *file_recovery)
{
  /*@ assert \valid_read(file_recovery); */
  /*@ assert valid_file_recovery(file_recovery); */
  /*@ assert file_recovery->file_size <= PHOTOREC_MAX_FILE_SIZE; */
  /*@ assert buffer_size <= 2 * PHOTOREC_MAX_BLOCKSIZE; */
  if(file_recovery->file_size + buffer_size/2 >= file_recovery->calculated_file_size)
  {
    /*@ assert valid_file_recovery(file_recovery); */
    return DC_STOP;
  }
  /*@ assert valid_file_recovery(file_recovery); */
  return DC_CONTINUE;
}

void file_check_size(file_recovery_t *file_recovery)
{
  /*@ assert \valid(file_recovery); */
  if(file_recovery->file_size<file_recovery->calculated_file_size)
    file_recovery->file_size=0;
  else
    file_recovery->file_size=file_recovery->calculated_file_size;
  /*@ assert valid_file_check_result(file_recovery); */
}

void file_check_size_min(file_recovery_t *file_recovery)
{
  /*@ assert \valid(file_recovery); */
  if(file_recovery->file_size<file_recovery->calculated_file_size)
    file_recovery->file_size=0;
  /*@ assert valid_file_check_result(file_recovery); */
}

void file_check_size_max(file_recovery_t *file_recovery)
{
  /*@ assert \valid(file_recovery); */
  if(file_recovery->file_size > file_recovery->calculated_file_size)
    file_recovery->file_size=file_recovery->calculated_file_size;
  /*@ assert valid_file_check_result(file_recovery); */
}

void reset_file_recovery(file_recovery_t *file_recovery)
{

  // Clear any existing memory buffer for this file
  file_buffer_clear(file_recovery);

  file_recovery->filename[0]='\0';
  file_recovery->time=0;
  file_recovery->file_stat=NULL;
  file_recovery->handle=NULL;
  file_recovery->file_size=0;
  file_recovery->location.list.prev=&file_recovery->location.list;
  file_recovery->location.list.next=&file_recovery->location.list;
  file_recovery->location.end=0;
  file_recovery->location.data=0;
  file_recovery->extension=NULL;
  file_recovery->min_filesize=0;
  file_recovery->calculated_file_size=0;
  file_recovery->data_check=NULL;
  file_recovery->file_check=NULL;
  file_recovery->file_rename=NULL;
  file_recovery->file_check_presave=NULL;
  file_recovery->offset_error=0;
  file_recovery->offset_ok=0;
  file_recovery->checkpoint_status=0;
  file_recovery->checkpoint_offset=0;
  file_recovery->flags=0;
  file_recovery->extra=0;
  file_recovery->data_check_tmp=0;
  file_recovery->image_data.width=0;   // FIXED: Activated for image filtering
  file_recovery->image_data.height=0;  // FIXED: Activated for image filtering
  // Free memory buffer BEFORE zeroing fields
  //free_memory_buffer(file_recovery);

}

file_stat_t * init_file_stats(file_enable_t *files_enable)
{
  file_stat_t *file_stats;
  file_enable_t *file_enable;
  unsigned int enable_count=1;	/* Lists are terminated by NULL */
  unsigned int sign_nbr;
  unsigned int i;
  /*@
    @ loop invariant valid_file_enable_node(file_enable);
    @ loop assigns enable_count, file_enable;
    @*/
  for(file_enable=files_enable;file_enable->file_hint!=NULL;file_enable++)
  {
    if(file_enable->enable>0 && file_enable->file_hint->register_header_check!=NULL)
    {
      enable_count++;
    }
  }
  /*@ assert enable_count > 0; */
  file_stats=(file_stat_t *)MALLOC(enable_count * sizeof(file_stat_t));
  /*@ assert \valid(file_stats + (0 .. enable_count-1)); */
  i=0;
  /*@
    @ loop invariant \valid(file_stats + (0 .. enable_count-1));
    @ loop invariant valid_file_enable_node(file_enable);
    @ loop invariant 1 <= enable_count;
    @ loop invariant 0 <= i < enable_count;
    @ loop invariant \forall integer j; 0 <= j < i ==> valid_file_stat(&file_stats[j]);
    @*/
  for(file_enable=files_enable;file_enable->file_hint!=NULL;file_enable++)
  {
    /*@ assert i < enable_count; */
    /*@ assert \valid_read(file_enable); */
    /*@ assert \valid_read(file_enable->file_hint); */
    if(file_enable->enable>0 && file_enable->file_hint->register_header_check!=NULL)
    {
      file_stats[i].file_hint=file_enable->file_hint;
      file_stats[i].not_recovered=0;
      file_stats[i].recovered=0;
      /*@ assert \valid_function((file_enable->file_hint)->register_header_check); */
      file_enable->file_hint->register_header_check(&file_stats[i]);
      /*@ assert valid_file_stat(&file_stats[i]); */
      i++;
    }
  }
  sign_nbr=index_header_check();
  /*@ assert \valid(file_stats + (0 .. enable_count-1)); */
  /*@ assert 1 <= enable_count; */
  file_stats[enable_count-1].file_hint=NULL;
#ifndef DISABLED_FOR_FRAMAC
  log_info("%u first-level signatures enabled\n", sign_nbr);
#endif
  return file_stats;
}

/*@
  @ requires \valid(file_recovery);
  @ requires valid_file_recovery(file_recovery);
  @ requires strlen(&file_recovery->filename[0]) > 0;
  @ requires valid_read_string(new_ext);
  @ requires strlen(new_ext) < (1<<30);
  @ requires separation: \separated(file_recovery, new_ext);
  @ ensures  valid_file_recovery(file_recovery);
  @ ensures file_recovery->file_size == \old(file_recovery->file_size);
  @*/
static int file_rename_aux(file_recovery_t *file_recovery, const char *new_ext)
{
  /*@ assert valid_file_recovery(file_recovery); */
  /*@ assert valid_string((char *)&file_recovery->filename); */
  char new_filename[sizeof(file_recovery->filename)];
  char *dst;
  char *dst_dir_sep;
  /*@ assert strlen((char *)&file_recovery->filename) < 2048; */
  /*@ assert strlen(new_ext) < (1<<30); */
  const unsigned int len=strlen(file_recovery->filename)+1+strlen(new_ext)+1;
  /*@ assert valid_read_string(&file_recovery->filename[0]); */
  if(len > sizeof(file_recovery->filename))
  {
    /*@ assert valid_string((char *)&file_recovery->filename); */
    /*@ assert valid_file_recovery(file_recovery); */
    return -1;
  }
  /*@ assert len <= sizeof(file_recovery->filename); */
  /*@ assert valid_read_string((char*)&file_recovery->filename); */
  /*@ assert \initialized((char *)&file_recovery->filename +(0..strlen(&file_recovery->filename[0]))); */
  /*@ assert valid_read_string(new_ext); */
  /*@ assert strlen(new_ext) < (1<<30); */
  /*@ assert \separated(file_recovery, new_ext); */
  memcpy(new_filename, (char *)&file_recovery->filename, sizeof(file_recovery->filename));
  /*@ assert valid_string(&new_filename[0]); */
  /*@ assert \initialized((char *)&new_filename[0] +(0..strlen(&new_filename[0]))); */
  /*@ assert valid_read_string(new_ext); */
  /*@ assert strlen(new_ext) < (1<<30); */
#ifdef DISABLED_FOR_FRAMAC
  dst_dir_sep=new_filename;
#else
  dst_dir_sep=strrchr(new_filename, '/');
  /*@ assert dst_dir_sep==\null || valid_string(dst_dir_sep); */
  /*@ assert dst_dir_sep==\null || \subset(dst_dir_sep, &new_filename[0] +(0..strlen(&new_filename[0]))); */
  /*@ assert dst_dir_sep==\null || \initialized(dst_dir_sep +(0..strlen(dst_dir_sep))); */
  if(dst_dir_sep==NULL)
    dst_dir_sep=new_filename;
#endif
  /*@ assert valid_string(dst_dir_sep); */
  /*@ assert \initialized((char *)dst_dir_sep +(0..strlen(dst_dir_sep))); */
  dst=dst_dir_sep;
  /*@ assert valid_string(dst); */
  /*@ assert \initialized(dst); */
  /*@ ghost char *odst = dst; */
  /*@
    @ loop invariant valid_string(dst);
    @ loop invariant \initialized(dst);
    @ loop invariant odst <= dst <= odst + strlen(odst);
    @ loop invariant valid_read_string(new_ext);
    @ loop invariant strlen(new_ext) < (1<<30);
    @ loop invariant valid_file_recovery(file_recovery);
    @ loop invariant valid_string(&new_filename[0]);
    @ loop assigns dst;
    @ loop variant strlen(dst);
    @*/
  while(*dst!='.' && *dst!='\0')
    dst++;
  /* Add extension */
  *dst++ = '.';
  /*@ assert valid_read_string(new_ext); */
  /*@ assert strlen(new_ext) < (1<<30); */
#ifdef DISABLED_FOR_FRAMAC
  memcpy(dst, new_ext, strlen(new_ext)+1);
#else
  strcpy(dst, new_ext);
#endif
  /*@ assert valid_string(dst); */
  /*@ assert valid_string(&new_filename[0]); */
  if(strlen(new_filename) >= sizeof(file_recovery->filename))
  {
    /*@ assert valid_read_string((const char *)&file_recovery->filename); */
    /*@ assert valid_file_recovery(file_recovery); */
    return -1;
  }
  /*@ assert valid_read_string(&new_filename[0]); */
  if(rename(&file_recovery->filename[0], new_filename)<0)
  {
    /* Rename has failed */
    /*@ assert valid_read_string((const char *)&file_recovery->filename); */
    /*@ assert valid_file_recovery(file_recovery); */
    return -1;
  }
  /*@ assert valid_file_recovery(file_recovery); */
  /*@ assert valid_read_string(&new_filename[0]); */
  memcpy(file_recovery->filename, new_filename, sizeof(file_recovery->filename));
  /*@ assert valid_read_string((const char *)&file_recovery->filename); */
  /*@ assert valid_file_recovery(file_recovery); */
  return 0;
}

/*@
  @ requires valid_string(filename);
  @ requires \valid(filename +(0..2047));
  @ requires 0 < strlen(filename) < 1<<30;
  @ requires 0 <= offset < buffer_size;
  @ requires buffer_size < 1<<30;
  @ requires \valid_read((char *)buffer+(0..buffer_size-1));
  @ requires new_ext==\null || (valid_read_string(new_ext) && strlen(new_ext) < 1<<30);
  @ requires \separated(filename, (char *)buffer+(0..buffer_size-1));
  @ requires \separated(filename, new_ext);
  @ ensures  new_ext==\null || (valid_read_string(new_ext) && strlen(new_ext) < 1<<30);
  @ ensures  valid_string(filename);
  @ ensures 0 < strlen(filename) < 1<<30;
  @*/
static int _file_rename(char *filename, const void *buffer, const int buffer_size, const int offset, const char *new_ext, const int append_original_ext)
{
  char *new_filename;
  const char *src=filename;
  const char *ext=NULL;
  char *dst;
  char *directory_sep;
  size_t len;
  len=strlen(src)+1;
  /*@ assert offset < buffer_size; */
  len+=buffer_size-offset+1;
  if(new_ext!=NULL)
    len+=strlen(new_ext)+1;
#ifndef DISABLED_FOR_FRAMAC
  new_filename=(char*)MALLOC(len);
  /*@ assert \valid(new_filename); */
  dst=new_filename;
  directory_sep=dst;
  strcpy(dst, src);
  /*@ ghost char *osrc = src; */
  /*@ ghost char *odst = dst; */
  /*@ assert valid_read_string(osrc); */
  //X loop assigns src, dst, odst[0..strlen(osrc)];
  //X loop assigns directory_sep, ext;
  /*@ loop invariant osrc <= src <= osrc + strlen(osrc);
    loop invariant odst <= dst <= odst + strlen(osrc);
    loop invariant valid_read_string(src);
    loop invariant dst - odst == src - osrc;
    loop invariant strlen(src) == strlen(osrc) - (src - osrc);
    loop invariant \forall integer i; 0 <= i < src - osrc ==> odst[i] == osrc[i];
    loop variant strlen(osrc) - (src - osrc);
    */
  while(*src!='\0')
  {
    if(*src=='/')
    {
      directory_sep=dst;
      ext=NULL;
    }
    if(*src=='.')
      ext=src;
    *dst++ = *src++;
  }
  *dst='\0';
  //@ assert *dst == '\0' && *src == '\0';
  //@ assert valid_string(odst);
  dst=directory_sep;
  /*@
    @ loop invariant valid_string(dst);
    @ loop assigns dst;
    @*/
  while(*dst!='.' && *dst!='\0')
    dst++;
  /* Add original filename */
  {
    char *dst_old=dst;
    /*@ assert valid_string(dst_old); */
    int off;
    int ok=0;
    int bad=0;
    *dst++ = '_';
    /*@
      @ loop invariant offset <= off <= buffer_size;
      @ loop variant buffer_size - off;
      @*/
    for(off=offset; off<buffer_size; off++)
    {
      const char c=((const char *)buffer)[off];
      if(c=='\0')
	break;
      switch(c)
      {
	case '/':
	case '\\':
	case ':':
	case '*':
	case '<':
	case '>':
	case '|':
	case '\'':
	  if(*(dst-1) != '_')
	    *dst++ = '_';
	  bad++;
	  break;
	default:
	  if(isprint(c) && !isspace(c) && !ispunct(c) && !iscntrl(c))
	  {
	    *dst++ = c;
	    ok++;
	  }
	  else
	  {
	    if(*(dst-1) != '_')
	      *dst++ = '_';
	    bad++;
	  }
	  break;
      }
    }
    if(ok <= bad)
      dst=dst_old;
    else
    {
      /*@
        @ loop invariant dst_old <= dst;
        @ loop assigns dst;
	@ loop variant dst;
	@*/
      while(dst > dst_old && *(dst-1)=='_')
	dst--;
    }
  }
  /* Add extension */
  if(new_ext!=NULL)
  {
    *dst++ = '.';
    strcpy(dst, new_ext);
  }
  else if(append_original_ext>0)
  {
    if(ext!=NULL)
    {
      strcpy(dst, ext);
    }
  }
  /*@ assert valid_read_string(new_filename); */
  /*@ assert valid_string(filename); */
  if(strlen(new_filename)<2048 && rename(filename, new_filename)==0)
  {
    strcpy(filename, new_filename);
    free(new_filename);
    /*@ assert valid_string(filename); */
    return 0;

  }
  free(new_filename);
#endif
  /*@ assert valid_string(filename); */
  return -1;
}

/* The original filename begins at offset in buffer and is null terminated */
int file_rename(file_recovery_t *file_recovery, const void *buffer, const int buffer_size, const int offset, const char *new_ext, const int append_original_ext)
{
  /*@ assert valid_file_recovery(file_recovery); */
  if(file_recovery->filename[0] == 0)
    return 0;
  /*@ assert strlen((char *)&file_recovery->filename) > 0; */
  /*@ assert new_ext==\null || valid_read_string(new_ext); */
  if(buffer!=NULL && 0 <= offset && offset < buffer_size &&
      _file_rename(file_recovery->filename, buffer, buffer_size, offset, new_ext, append_original_ext)==0)
  {
    /*@ assert valid_file_recovery(file_recovery); */
    return 0;
  }
  /*@ assert valid_file_recovery(file_recovery); */
  /*@ assert valid_string((char *)(&file_recovery->filename)); */
  /*@ assert new_ext==\null || valid_read_string(new_ext); */
  if(new_ext==NULL)
    return 0;
  /* Try without the original filename */
  return file_rename_aux(file_recovery, new_ext);
}

/* The original filename begins at offset in buffer and is null terminated */
/*@
  @ requires \valid(file_recovery);
  @ requires strlen((char*)&file_recovery->filename) < 1<<30;
  @ requires valid_file_recovery(file_recovery);
  @ requires valid_read_string((char*)&file_recovery->filename);
  @ requires 0 <= offset < buffer_size;
  @ requires buffer_size < 1<<30;
  @ requires \valid_read((char *)buffer+(0..buffer_size-1));
  @ requires new_ext==\null || (valid_read_string(new_ext) && strlen(new_ext) < 1<<30);
  @ requires \separated(file_recovery, new_ext);
  @ ensures  new_ext==\null || (valid_read_string(new_ext) && strlen(new_ext) < 1<<30);
  @ ensures  valid_read_string((char*)&file_recovery->filename);
  @ ensures  valid_file_recovery(file_recovery);
  @ ensures file_recovery->file_size == \old(file_recovery->file_size);
  @*/
static int _file_rename_unicode(file_recovery_t *file_recovery, const void *buffer, const int buffer_size, const int offset, const char *new_ext, const int append_original_ext)
{
  char *new_filename;
  const char *src=file_recovery->filename;
  const char *src_ext=src;
  char *dst;
  char *dst_dir_sep;
  size_t len=strlen(src)+1;
  /*@ assert offset < buffer_size; */
  len+=buffer_size-offset;
  if(new_ext!=NULL)
    len+=strlen(new_ext);
#ifndef DISABLED_FOR_FRAMAC
  new_filename=(char*)MALLOC(len);
  /*@ assert \valid(new_filename); */
  dst=new_filename;
  dst_dir_sep=dst;
  while(*src!='\0')
  {
    if(*src=='/')
      dst_dir_sep=dst;
    if(*src=='.')
      src_ext=src;
    *dst++ = *src++;
  }
  *dst='\0';
  dst=dst_dir_sep;
  while(*dst!='.' && *dst!='\0')
    dst++;
  /* Add original filename */
  {
    char *dst_old=dst;
    int off;
    int ok=0;
    int bad=0;
    *dst++ = '_';
    src=&((const char *)buffer)[offset];
    for(off=offset; off<buffer_size && *src!='\0'; off+=2, src+=2)
    {
      switch(*src)
      {
	case '/':
	case '\\':
	case ':':
	case '*':
	case '<':
	case '>':
	case '|':
	case '\'':
	  if(*(dst-1) != '_')
	    *dst++ = '_';
	  bad++;
	  break;
	default:
	  if(isprint(*src) && !isspace(*src) && !ispunct(*src) && !iscntrl(*src))
	  {
	    *dst++ = *src;
	    ok++;
	  }
	  else
	  {
	    if(*(dst-1) != '_')
	      *dst++ = '_';
	    bad++;
	  }
	  break;
      }
    }
    if(ok <= bad)
      dst=dst_old;
    else
    {
      while(dst > dst_old && *(dst-1)=='_')
	dst--;
    }
  }
  /* Add extension */
  if(new_ext!=NULL)
  {
    src=new_ext;
    *dst++ = '.';
    while(*src!='\0')
      *dst++ = *src++;
  }
  else if(append_original_ext>0 && src_ext!=NULL)
  {
    while(*src_ext!='\0')
      *dst++ = *src_ext++;
  }
  *dst='\0';
  if(strlen(new_filename)<sizeof(file_recovery->filename) && rename(file_recovery->filename, new_filename)==0)
  {
    strcpy(file_recovery->filename, new_filename);
    free(new_filename);
    /*@ assert valid_read_string(&file_recovery->filename[0]); */
    return 0;
  }
  free(new_filename);
#endif
  /*@ assert valid_read_string(&file_recovery->filename[0]); */
  /*@ assert valid_file_recovery(file_recovery); */
  return -1;
}

int file_rename_unicode(file_recovery_t *file_recovery, const void *buffer, const int buffer_size, const int offset, const char *new_ext, const int append_original_ext)
{
  if(buffer!=NULL && 0 <= offset && offset < buffer_size &&
      _file_rename_unicode(file_recovery, buffer, buffer_size, offset, new_ext, append_original_ext)==0)
    return 0;
  /*@ assert valid_file_recovery(file_recovery); */
  if(new_ext==NULL)
    return 0;
  return file_rename_aux(file_recovery, new_ext);
}

/*@
  @ assigns offset_skipped_header;
  @*/
void header_ignored_cond_reset(uint64_t start, uint64_t end)
{
  if(start <= offset_skipped_header && offset_skipped_header <= end)
    offset_skipped_header=0;
}

/* 0: file_recovery_new->location.start has been taken into account, offset_skipped_header may have been updated
 * 1: file_recovery_new->location.start has been ignored */
int header_ignored_adv(const file_recovery_t *file_recovery, const file_recovery_t *file_recovery_new)
{
  /*@ assert \separated(file_recovery, file_recovery->handle, file_recovery_new, &errno, &offset_skipped_header); */
  file_recovery_t fr_test;
  off_t offset;
  assert(file_recovery!=NULL);
  assert(file_recovery_new!=NULL);
  /*@ assert \valid_read(file_recovery); */
  /*@ assert \valid_read(file_recovery_new); */
  if(file_recovery->file_check==NULL)
  {
    log_warning("header_ignored_adv: file_check==NULL\n");
    /*@ assert \valid_read(file_recovery); */
    /*@ assert \valid_read(file_recovery_new); */
    return 1;
  }
  if(file_recovery->handle==NULL)
  {
    if(file_recovery_new->location.start < offset_skipped_header || offset_skipped_header==0)
    {
      offset_skipped_header=file_recovery_new->location.start;
    }
    /*@ assert \valid_read(file_recovery); */
    /*@ assert \valid_read(file_recovery_new); */
    return 0;
  }

  memcpy(&fr_test, file_recovery, sizeof(fr_test));
#if defined(HAVE_FTELLO)
  if((offset=ftello(file_recovery->handle)) < 0)
    offset=ftell(file_recovery->handle);
#else
  offset=ftell(file_recovery->handle);
#endif
  assert(offset >= 0);
  file_recovery->file_check(&fr_test);
  if(my_fseek(file_recovery->handle, offset, SEEK_SET) < 0)
  {
    log_error("BUG in header_ignored_adv: my_fseek() failed\n");
    /*@ assert \valid_read(file_recovery); */
    /*@ assert \valid_read(file_recovery_new); */
    return 1;
  }
  if(fr_test.file_size>0)
    return 1;
  if(file_recovery_new->location.start < offset_skipped_header || offset_skipped_header==0)
  {
    offset_skipped_header=file_recovery_new->location.start;
  }
  /*@ assert \valid_read(file_recovery); */
  /*@ assert \valid_read(file_recovery_new); */
  return 0;
}

/*@
  @ requires \separated(file_recovery_new, &offset_skipped_header);
  @ assigns offset_skipped_header;
  @*/
void header_ignored(const file_recovery_t *file_recovery_new)
{
  if(file_recovery_new==NULL)
  {
    offset_skipped_header=0;
    return ;
  }
  /*@ assert \valid_read(file_recovery_new); */
  if(file_recovery_new->location.start < offset_skipped_header || offset_skipped_header==0)
    offset_skipped_header=file_recovery_new->location.start;
}

/*@
  @ requires \separated(list_search_space, current_search_space, offset, &gpls_nbr, &offset_skipped_header);
  @ assigns gpls_nbr, offset_skipped_header, *current_search_space, *offset;
  @*/
void get_prev_location_smart(const alloc_data_t *list_search_space, alloc_data_t **current_search_space, uint64_t *offset, const uint64_t prev_location)
{
  alloc_data_t *file_space=*current_search_space;
  if(offset_skipped_header==0)
    return ;
#ifndef __FRAMAC__
  gpls_nbr++;
#endif
  /*@
    @ loop invariant \valid_read(file_space);
    @ loop invariant \separated(file_space, current_search_space, offset);
    @ loop assigns file_space, offset_skipped_header, *current_search_space, *offset;
    @*/
  while(1)
  {
    file_space=td_list_prev_entry(file_space, list);
    /*@ assert \valid_read(file_space); */
    if(file_space==list_search_space)
      break;
    if(file_space->start <= offset_skipped_header && offset_skipped_header < file_space->end)
    {
      *current_search_space=file_space;
      *offset=offset_skipped_header;
      offset_skipped_header=0;
      return ;
    }
    if(file_space->start < prev_location)
      break;
  }
#ifdef DEBUG_PREV_LOCATION
  log_info("get_prev_location_smart: reset offset_skipped_header=%llu, offset=%llu\n",
      (long long unsigned)(offset_skipped_header/512),
      (long long unsigned)(*offset/512));
#endif
  /*@
    @ loop invariant \valid_read(file_space);
    @ loop invariant \separated(file_space, current_search_space, offset);
    @ loop assigns file_space, offset_skipped_header, *current_search_space, *offset;
    @*/
  while(1)
  {
    file_space=td_list_prev_entry(file_space, list);
    /*@ assert \valid_read(file_space); */
    if(file_space==list_search_space)
    {
      offset_skipped_header=0;
      return;
    }
    *current_search_space=file_space;
    if(file_space->start < offset_skipped_header)
    {
#ifdef DEBUG_PREV_LOCATION
      log_info("get_prev_location_smart: file_space->start < offset_skipped_header, prev_location=%llu (in 512-bytes sectors), offset=%llu => %llu\n",
	  (long long unsigned)(prev_location/512),
	  (long long unsigned)(*offset/512),
	  (long long unsigned)(offset_skipped_header/512));
#endif
      *offset=offset_skipped_header;
      offset_skipped_header=0;
      return ;
    }
    *offset=file_space->start;
  }
}

int my_fseek(FILE *stream, off_t offset, int whence)
{
#if defined(HAVE_FSEEKO) && !defined(__MINGW32__) && !defined(__ARM_EABI__)
  {
    int res;
    if((res=fseeko(stream, offset, whence))>=0)
      return res;
  }
#endif
 return fseek(stream, offset, whence);
}

time_t get_time_from_YYMMDDHHMMSS(const char *date_asc)
{
  struct tm tm_time;
  tm_time.tm_sec=(date_asc[10]-'0')*10+(date_asc[11]-'0');	/* seconds 0-59 */
  tm_time.tm_min=(date_asc[8]-'0')*10+(date_asc[9]-'0');      /* minutes 0-59 */
  tm_time.tm_hour=(date_asc[6]-'0')*10+(date_asc[7]-'0');     /* hours   0-23*/
  tm_time.tm_mday=(date_asc[4]-'0')*10+(date_asc[5]-'0');	/* day of the month 1-31 */
  tm_time.tm_mon=(date_asc[2]-'0')*10+(date_asc[3]-'0')-1;	/* month 1-12 */
  tm_time.tm_year=(date_asc[0]-'0')*10+(date_asc[1]-'0');        	/* year */
  if(tm_time.tm_year<80)
    tm_time.tm_year+=100;	/* year 2000 - 2079 */
  tm_time.tm_isdst = -1;	/* unknown daylight saving time */
  return mktime(&tm_time);
}

time_t get_time_from_YYYY_MM_DD_HH_MM_SS(const unsigned char *date_asc)
{
  struct tm tm_time;
  if(memcmp(date_asc, "0000", 4)==0)
    return (time_t)0;
  tm_time.tm_sec=(date_asc[17]-'0')*10+(date_asc[18]-'0');      /* seconds 0-59 */
  tm_time.tm_min=(date_asc[14]-'0')*10+(date_asc[15]-'0');      /* minutes 0-59 */
  tm_time.tm_hour=(date_asc[11]-'0')*10+(date_asc[12]-'0');     /* hours   0-23*/
  tm_time.tm_mday=(date_asc[8]-'0')*10+(date_asc[9]-'0');	/* day of the month 1-31 */
  tm_time.tm_mon=(date_asc[5]-'0')*10+(date_asc[6]-'0')-1;	/* month 0-11 */
  tm_time.tm_year=(date_asc[0]-'0')*1000+(date_asc[1]-'0')*100+
    (date_asc[2]-'0')*10+(date_asc[3]-'0')-1900;        	/* year */
  tm_time.tm_isdst = -1;		/* unknown daylight saving time */
  return mktime(&tm_time);
}

time_t get_time_from_YYYY_MM_DD_HHMMSS(const char *date_asc)
{
  struct tm tm_time;
  if(memcmp(date_asc, "0000", 4)==0)
    return (time_t)0;
  tm_time.tm_sec=(date_asc[15]-'0')*10+(date_asc[16]-'0');      /* seconds 0-59 */
  tm_time.tm_min=(date_asc[13]-'0')*10+(date_asc[14]-'0');      /* minutes 0-59 */
  tm_time.tm_hour=(date_asc[11]-'0')*10+(date_asc[12]-'0');     /* hours   0-23*/
  tm_time.tm_mday=(date_asc[8]-'0')*10+(date_asc[9]-'0');	/* day of the month 1-31 */
  tm_time.tm_mon=(date_asc[5]-'0')*10+(date_asc[6]-'0')-1;	/* month 0-11 */
  tm_time.tm_year=(date_asc[0]-'0')*1000+(date_asc[1]-'0')*100+
    (date_asc[2]-'0')*10+(date_asc[3]-'0')-1900;        	/* year */
  tm_time.tm_isdst = -1;		/* unknown daylight saving time */
  return mktime(&tm_time);
}

time_t get_time_from_YYYYMMDD_HHMMSS(const char *date_asc)
{
  struct tm tm_time;
  tm_time.tm_sec=(date_asc[13]-'0')*10+(date_asc[14]-'0');      /* seconds 0-59 */
  tm_time.tm_min=(date_asc[11]-'0')*10+(date_asc[12]-'0');      /* minutes 0-59 */
  tm_time.tm_hour=(date_asc[9]-'0')*10+(date_asc[10]-'0');      /* hours   0-23*/
  tm_time.tm_mday=(date_asc[6]-'0')*10+(date_asc[7]-'0');	/* day of the month 1-31 */
  tm_time.tm_mon=(date_asc[4]-'0')*10+(date_asc[5]-'0')-1;	/* month 0-11 */
  tm_time.tm_year=(date_asc[0]-'0')*1000+(date_asc[1]-'0')*100+
    (date_asc[2]-'0')*10+(date_asc[3]-'0')-1900;		/* year */
  tm_time.tm_isdst = -1;		/* unknown daylight saving time */
  return mktime(&tm_time);
}

// Global file size filter for all recovery operations (copy, not pointer!)
static file_size_filter_t global_file_size_filter = {0, 0};

// Helper functions for user filesize limit checking

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

// Check if user has filesize filters active
static int has_user_filesize_limits(void)
{
  return (global_file_size_filter.min_file_size > 0 ||
          global_file_size_filter.max_file_size > 0);
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

// Memory buffer for each file recovery with hash table lookup
#define MAX_FILE_BUFFERS 100
#define HASH_TABLE_SIZE 211 // Prime number for better distribution

// Statistics for monitoring buffer vs disk usage
static struct {
    unsigned long buffer_writes;      // Successful buffer writes
    unsigned long disk_fallback_full; // Fallback due to buffer pool full
    unsigned long disk_fallback_size; // Fallback due to file too large
    unsigned long disk_fallback_oom;  // Fallback due to malloc/realloc failure
} buffer_stats = {0, 0, 0, 0};

static struct {
    uint64_t location_start;  // FIXED: Use location.start as key instead of filename
    unsigned char *buffer;
    size_t buffer_size;
    size_t buffer_capacity;
    int next_index; // For collision chaining, -1 means end of chain
} file_buffers[MAX_FILE_BUFFERS];

static int hash_table[HASH_TABLE_SIZE]; // Index into file_buffers, -1 means empty
static int buffer_count = 0;

// FIXED: Simple hash function for location.start instead of filename
static int hash_location(uint64_t location_start) {
    // Simple hash for 64-bit location values
    uint32_t high = (uint32_t)(location_start >> 32);
    uint32_t low = (uint32_t)(location_start & 0xFFFFFFFF);
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
        }
        initialized = 1;
    }
}

// FIXED: Find or create buffer for file using location.start as key
static int get_buffer_index(file_recovery_t *file_recovery)
{
    int hash;
    int idx;
    int i;
    uint64_t max_filesize;

    init_buffer_hash_table();

    hash = hash_location(file_recovery->location.start);
    idx = hash_table[hash];

    // Search collision chain
    while (idx != -1) {
        if (file_buffers[idx].location_start == file_recovery->location.start) {
            return idx;
        }
        idx = file_buffers[idx].next_index;
    }

    // Create new buffer
    if (buffer_count >= MAX_FILE_BUFFERS) {
        return -1; // Too many buffers
    }

    i = buffer_count++;
    file_buffers[i].location_start = file_recovery->location.start;

    // Smart initial allocation based on file type
    max_filesize = get_max_filesize_for_buffer(file_recovery);
    {
        size_t initial_size = (max_filesize > 1024*1024) ? 1024*1024 : (size_t)max_filesize; // Start with 1MB or file max, whichever is smaller

        file_buffers[i].buffer = malloc(initial_size);
        file_buffers[i].buffer_size = 0;
        file_buffers[i].buffer_capacity = initial_size;
        file_buffers[i].next_index = -1;
    }

    if (!file_buffers[i].buffer) {
        buffer_count--;
        return -1;
    }

    // Add to hash table (insert at head of collision chain)
    file_buffers[i].next_index = hash_table[hash];
    hash_table[hash] = i;

    return i;
}

// Memory buffer writing
int file_buffer_write(file_recovery_t *file_recovery, const void *data, size_t size)
{
    int idx;
    uint64_t user_min;
    uint64_t user_max;
    uint64_t max_filesize;
    uint64_t current_size;
    uint64_t new_size;

    if (!file_recovery || !data || size == 0) {
        return -1;
    }

    idx = get_buffer_index(file_recovery);
    if (idx < 0) {
        // Fallback to direct write if buffer fails
        buffer_stats.disk_fallback_full++;
        if (!file_recovery->handle) return -1;

        // Check user file size filters before direct write
        user_min = get_user_min_filesize();
        user_max = get_user_max_filesize();
        current_size = file_recovery->file_size + size;

        if (user_min > 0 && current_size < user_min) {
            return 0; // Pretend success but don't write
        }
        if (user_max > 0 && current_size > user_max) {
            return 0; // Pretend success but don't write
        }

        return (fwrite(data, 1, size, file_recovery->handle) == size) ? 0 : -1;
    }

    // NEW: Check user file size limits BEFORE buffer operations
    user_min = get_user_min_filesize();
    user_max = get_user_max_filesize();
    new_size = file_recovery->file_size + size;

    if ((user_min > 0 && new_size < user_min) ||
        (user_max > 0 && new_size > user_max)) {
        // File size outside user limits - just ignore this write (successful no-op)
        return 0;
    }

    // Check if we exceed max file size for this file type (fallback behavior when no user limits)
    max_filesize = get_max_filesize_for_buffer(file_recovery);
    if (file_buffers[idx].buffer_size + size > max_filesize) {
        // File too large for buffer, fallback to direct write (only when no user limits set)
        if (!has_user_filesize_limits()) {
            buffer_stats.disk_fallback_size++;
            if (!file_recovery->handle) return -1;
            return (fwrite(data, 1, size, file_recovery->handle) == size) ? 0 : -1;
        } else {
            // User has limits set - this should have been caught above, but safety check
            return 0;
        }
    }

    // Expand buffer if needed with smarter allocation strategy
    if (file_buffers[idx].buffer_size + size > file_buffers[idx].buffer_capacity) {
        // Instead of doubling, grow by chunks but respect max_filesize
        size_t chunk_size = (max_filesize > 10*1024*1024) ? 1024*1024 : max_filesize/4; // 1MB or 25% of max
        size_t needed = file_buffers[idx].buffer_size + size;
        size_t new_capacity = ((needed + chunk_size - 1) / chunk_size) * chunk_size; // Round up to chunk boundary

        // Cap at max_filesize
        if (new_capacity > max_filesize) {
            new_capacity = max_filesize;
        }

        unsigned char *new_buffer = realloc(file_buffers[idx].buffer, new_capacity);
        if (!new_buffer) {
            // Fallback to direct write
            buffer_stats.disk_fallback_oom++;
            if (!file_recovery->handle) return -1;
            return (fwrite(data, 1, size, file_recovery->handle) == size) ? 0 : -1;
        }
        file_buffers[idx].buffer = new_buffer;
        file_buffers[idx].buffer_capacity = new_capacity;
    }

    // Add to buffer
    memcpy(file_buffers[idx].buffer + file_buffers[idx].buffer_size, data, size);
    file_buffers[idx].buffer_size += size;

    // NOTE: file_size is already updated by PhotoRec in phbf.c, don't double-update
    buffer_stats.buffer_writes++;

    // Log stats periodically
    print_buffer_statistics();

    return 0;
}

// Print buffer statistics as JSON to log file
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

    if (total_writes > 0) {
        FILE *log_file = fopen("/home/piotr/buffer_stats.json", "a");
        if (log_file) {
            fprintf(log_file,
                "{\"timestamp\":%ld,"
                "\"buffer_writes\":%lu,"
                "\"disk_fallback_full\":%lu,"
                "\"disk_fallback_size\":%lu,"
                "\"disk_fallback_oom\":%lu,"
                "\"total_writes\":%lu,"
                "\"buffer_rate\":%.1f}\n",
                current_time,
                buffer_stats.buffer_writes,
                buffer_stats.disk_fallback_full,
                buffer_stats.disk_fallback_size,
                buffer_stats.disk_fallback_oom,
                total_writes,
                (buffer_stats.buffer_writes * 100.0) / total_writes);
            fclose(log_file);
        }
    }
}

// Get buffer data for file_check functions to work on memory instead of disk
const unsigned char* file_buffer_get_data(file_recovery_t *file_recovery, size_t *buffer_size)
{
    if (!file_recovery || !buffer_size) {
        return NULL;
    }

    init_buffer_hash_table();

    int hash = hash_location(file_recovery->location.start);
    int idx = hash_table[hash];

    // Search collision chain
    while (idx != -1) {
        if (file_buffers[idx].location_start == file_recovery->location.start) {
            *buffer_size = file_buffers[idx].buffer_size;
            return (const unsigned char*)file_buffers[idx].buffer;
        }
        idx = file_buffers[idx].next_index;
    }

    *buffer_size = 0;
    return NULL;
}

// Helper function for file_check functions - returns 1 if should use buffer instead of disk
int read_file_data_from_buffer(file_recovery_t *file_recovery)
{
  // Check if file data is in memory buffer instead of on disk
  size_t buffer_size;
  const unsigned char *buffer_data = file_buffer_get_data(file_recovery, &buffer_size);
  if (buffer_data && buffer_size > 0) {
    // File is in memory buffer, use simple size check instead of complex disk validation
    file_recovery->file_size = file_recovery->calculated_file_size;
    return 1;
  }
  return 0;
}

// FIXED: Remove buffer from hash table (helper function)
static void remove_buffer_from_hash_table(int buffer_idx) {
    int hash;
    int idx, prev_idx;

    // Find and remove from hash table
    hash = hash_location(file_buffers[buffer_idx].location_start);
    idx = hash_table[hash];
    prev_idx = -1;

    while (idx != -1) {
        if (idx == buffer_idx) {
            // Found it, remove from chain
            if (prev_idx == -1) {
                // It's the head of the chain
                hash_table[hash] = file_buffers[idx].next_index;
            } else {
                // It's in the middle/end of chain
                file_buffers[prev_idx].next_index = file_buffers[idx].next_index;
            }
            break;
        }
        prev_idx = idx;
        idx = file_buffers[idx].next_index;
    }
}

// Clear buffer without writing to disk (for discarded files)
int file_buffer_clear(file_recovery_t *file_recovery)
{
    int hash;
    int idx;
    int last_idx;
    int moved_hash;

    if (!file_recovery) return 0;

    init_buffer_hash_table();
    hash = hash_location(file_recovery->location.start);
    idx = hash_table[hash];

    // Search collision chain
    while (idx != -1) {
        if (file_buffers[idx].location_start == file_recovery->location.start) {
            // Found it, remove from hash table first
            remove_buffer_from_hash_table(idx);

            // Free buffer
            free(file_buffers[idx].buffer);

            // Move last buffer to this position and update hash table
            if (idx < buffer_count - 1) {
                last_idx = buffer_count - 1;
                remove_buffer_from_hash_table(last_idx); // Remove old location
                file_buffers[idx] = file_buffers[last_idx]; // Move

                // Re-insert moved buffer into hash table
                moved_hash = hash_location(file_buffers[idx].location_start);
                file_buffers[idx].next_index = hash_table[moved_hash];
                hash_table[moved_hash] = idx;
            }
            buffer_count--;
            return 0;
        }
        idx = file_buffers[idx].next_index;
    }
    return 0; // Buffer not found, already cleared
}

// Flush buffer to disk and free memory
int file_buffer_flush(file_recovery_t *file_recovery)
{
    int hash;
    int idx;
    int last_idx;
    int moved_hash;

    if (!file_recovery) return 0;

    init_buffer_hash_table();
    hash = hash_location(file_recovery->location.start);
    idx = hash_table[hash];

    // Search collision chain
    while (idx != -1) {
        if (file_buffers[idx].location_start == file_recovery->location.start) {
            // Write to disk if handle available
            if (file_recovery->handle && file_buffers[idx].buffer_size > 0) {
                // Check user file size filters before writing to disk
                uint64_t user_min = get_user_min_filesize();
                uint64_t user_max = get_user_max_filesize();

                // Check if file size is within user limits
                if (user_min > 0 && file_buffers[idx].buffer_size < user_min) {
                    printf("DEBUG file_buffer_flush: REJECTING file too small (%lu < %lu)\n",
                           (unsigned long)file_buffers[idx].buffer_size, (unsigned long)user_min);
                    // Don't write - just clean up buffer and return success
                } else if (user_max > 0 && file_buffers[idx].buffer_size > user_max) {
                    printf("DEBUG file_buffer_flush: REJECTING file too large (%lu > %lu)\n",
                           (unsigned long)file_buffers[idx].buffer_size, (unsigned long)user_max);
                    // Don't write - just clean up buffer and return success
                } else {
                    // File size is OK - write to disk
                    if (fwrite(file_buffers[idx].buffer, 1, file_buffers[idx].buffer_size,
                              file_recovery->handle) != file_buffers[idx].buffer_size) {
                        return -1;
                    }
                }
            }

            // Same cleanup logic as file_buffer_clear
            remove_buffer_from_hash_table(idx);
            free(file_buffers[idx].buffer);

            // Move last buffer to this position and update hash table
            if (idx < buffer_count - 1) {
                last_idx = buffer_count - 1;
                remove_buffer_from_hash_table(last_idx);
                file_buffers[idx] = file_buffers[last_idx];

                // Re-insert moved buffer into hash table
                moved_hash = hash_location(file_buffers[idx].location_start);
                file_buffers[idx].next_index = hash_table[moved_hash];
                hash_table[moved_hash] = idx;
            }
            buffer_count--;
            return 0;
        }
        idx = file_buffers[idx].next_index;
    }
    return 0; // Buffer not found - OK
}
