/*

    File: phrecn.c

    Copyright (C) 1998-2009 Christophe GRENIER <grenier@cgsecurity.org>

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

#if defined(DISABLED_FOR_FRAMAC)
#undef HAVE_NCURSES
#undef ENABLE_DFXML
#endif

#include <stdio.h>
#ifdef HAVE_STDLIB_H
#include <stdlib.h>
#endif
#include <stdint.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>	/* unlink, ftruncate */
#endif
#ifdef HAVE_STRING_H
#include <string.h>
#endif
#ifdef HAVE_TIME_H
#include <time.h>
#endif
#ifdef HAVE_SYS_TIME_H
#include <sys/time.h>
#endif
#include <ctype.h>      /* tolower */
#include "types.h"
#include "common.h"
#include "intrf.h"
#ifdef HAVE_NCURSES
#include "intrfn.h"
#endif
#include <errno.h>
#ifdef HAVE_WINDEF_H
#include <windef.h>
#endif
#ifdef HAVE_WINBASE_H
#include <stdarg.h>
#include <winbase.h>
#endif
#include "dir.h"
#include "fat.h"
#include "fat_dir.h"
#include "list.h"
#include "lang.h"
#include "filegen.h"
#include "photorec.h"
#include "image_filter.h"
#include "sessionp.h"
#include "phrecn.h"
#include "log.h"
#include "json_log.h"
#include "log_part.h"
#include "file_tar.h"
#include "phcfg.h"
#include "pblocksize.h"
#include "askloc.h"
#include "fat_unformat.h"
#include "pnext.h"
#include "phbf.h"
#include "phnc.h"
#include "phbs.h"

/* Global variables to store original format user entered for pixels */
static char pixels_min_format[32] = "";
static char pixels_max_format[32] = "";
#include "file_found.h"
#include "dfxml.h"
#include "poptions.h"
#include "psearchn.h"

/* #define DEBUG */
/* #define DEBUG_BF */
#define DEFAULT_IMAGE_NAME "image_remaining.dd"

extern int need_to_stop;

static int interface_cannot_create_file(void);

#ifdef HAVE_NCURSES
static void recovery_finished(disk_t *disk, const partition_t *partition, const unsigned int file_nbr, const char *recup_dir, const pstatus_t ind_stop)
{
  aff_copy(stdscr);
  wmove(stdscr,4,0);
  wprintw(stdscr,"%s", disk->description_short(disk));
  mvwaddstr(stdscr,5,0,msg_PART_HEADER_LONG);
  wmove(stdscr,6,0);
  aff_part(stdscr,AFF_PART_ORDER|AFF_PART_STATUS, disk, partition);
  wmove(stdscr,9,0);
  wclrtoeol(stdscr);
  wprintw(stdscr,"%u files saved in %s directory.\n", file_nbr, recup_dir);
  wmove(stdscr,10,0);
  wclrtoeol(stdscr);
  switch(ind_stop)
  {
    case PSTATUS_OK:
      wprintw(stdscr,"Recovery completed.");
      if(file_nbr > 0)
      {
	wmove(stdscr, 12, 0);
	wprintw(stdscr, "You are welcome to donate to support and encourage further development");
	wmove(stdscr, 13, 0);
	wprintw(stdscr, "https://www.cgsecurity.org/wiki/Donation");
      }
      break;
    case PSTATUS_STOP:
      wprintw(stdscr,"Recovery aborted by the user.");
      break;
    case PSTATUS_EACCES:
      wprintw(stdscr,"Cannot create file in current directory.");
      break;
    case PSTATUS_ENOSPC:
      wprintw(stdscr,"Cannot write file, no space left.");
      break;
  }
  wmove(stdscr,22,0);
  wclrtoeol(stdscr);
  wattrset(stdscr, A_REVERSE);
  waddstr(stdscr,"[ Quit ]");
  wattroff(stdscr, A_REVERSE);
  wrefresh(stdscr);
  log_flush();
  while(1)
  {
    switch(wgetch(stdscr))
    {
      case KEY_ENTER:
#ifdef PADENTER
      case PADENTER:
#endif
      case '\n':
      case '\r':
      case 'q':
      case 'Q':
	return;
    }
  }
}
#endif

#if defined(HAVE_NCURSES) && (defined(__CYGWIN__) || defined(__MINGW32__))
static int interface_cannot_create_file(void)
{
  static const struct MenuItem menuMain[]=
  {
    { 'C', "Continue", "Continue the recovery."},
    { 'Q', "Quit", "Abort the recovery."},
    { 0,NULL,NULL}
  };
  unsigned int menu=0;
  int car;
  aff_copy(stdscr);
  wmove(stdscr,4,0);
  wprintw(stdscr,"PhotoRec has been unable to create new file.");
  wmove(stdscr,5,0);
  wprintw(stdscr,"This problem may be due to antivirus blocking write access while scanning files created by PhotoRec.");
  wmove(stdscr,6,0);
  wprintw(stdscr,"If possible, temporarily disable your live antivirus protection.");
  car= wmenuSelect_ext(stdscr, 23, INTER_MAIN_Y, INTER_MAIN_X, menuMain, 10,
      "CQ", MENU_VERT | MENU_VERT_WARN | MENU_BUTTON, &menu,NULL);
  if(car=='c' || car=='C')
    return 0;
  return 1;
}
#else
/*@ assigns \nothing; */
static int interface_cannot_create_file(void)
{
  return 1;
}
#endif

#ifdef HAVE_NCURSES
/*@
  @ requires valid_read_string(filename);
  @ requires \valid_read(list_search_space);
  @*/
static void gen_image(const char *filename, disk_t *disk, const alloc_data_t *list_search_space)
{
  struct td_list_head *search_walker = NULL;
  const unsigned int buffer_size=64*512;
  FILE *out;
  unsigned char *buffer;
  if(td_list_empty(&list_search_space->list))
    return ;
  if(!(out=fopen(filename,"w+b")))
    return ;
  buffer=(unsigned char *)MALLOC(buffer_size);
  td_list_for_each(search_walker, &list_search_space->list)
  {
    uint64_t offset;
    alloc_data_t *current_search_space;
    current_search_space=td_list_entry(search_walker, alloc_data_t, list);
    for(offset=current_search_space->start; offset <= current_search_space->end; offset+=buffer_size)
    {
      const unsigned int read_size=(current_search_space->end - offset + 1 < buffer_size ?
	  current_search_space->end - offset + 1 : buffer_size);
      disk->pread(disk, buffer, read_size, offset);
      if(fwrite(buffer, read_size, 1, out)<1)
      {
	log_critical("Cannot write to file %s: %s\n", filename, strerror(errno));
	free(buffer);
	fclose(out);
	return ;
      }
    }
  }
  free(buffer);
  fclose(out);
}
#endif

int photorec(struct ph_param *params, const struct ph_options *options, alloc_data_t *list_search_space)
{
  pstatus_t ind_stop=PSTATUS_OK;
  const unsigned int blocksize_is_known=params->blocksize;
  /*@ assert valid_read_string(params->recup_dir); */
  params_reset(params, options);
  /*@ assert valid_read_string(params->recup_dir); */
  if(params->cmd_run!=NULL && params->cmd_run[0]!='\0')
  {
    skip_comma_in_command(&params->cmd_run);
    /*@ assert valid_read_string(params->recup_dir); */
#ifndef DISABLED_FOR_FRAMAC
    if(check_command(&params->cmd_run,"status=unformat",15)==0)
    {
      params->status=STATUS_UNFORMAT;
    }
    else if(check_command(&params->cmd_run,"status=find_offset",18)==0)
    {
      params->status=STATUS_FIND_OFFSET;
    }
    else if(check_command(&params->cmd_run,"status=ext2_on_bf",17)==0)
    {
      params->status=STATUS_EXT2_ON_BF;
    }
    else if(check_command(&params->cmd_run,"status=ext2_on_save_everything",30)==0)
    {
      params->status=STATUS_EXT2_ON_SAVE_EVERYTHING;
    }
    else if(check_command(&params->cmd_run,"status=ext2_on",14)==0)
    {
      params->status=STATUS_EXT2_ON;
    }
    else if(check_command(&params->cmd_run,"status=ext2_off_bf",18)==0)
    {
      params->status=STATUS_EXT2_OFF_BF;
    }
    else if(check_command(&params->cmd_run,"status=ext2_off_save_everything",31)==0)
    {
      params->status=STATUS_EXT2_OFF_SAVE_EVERYTHING;
    }
    else if(check_command(&params->cmd_run,"status=ext2_off",15)==0)
    {
      params->status=STATUS_EXT2_OFF;
    }
#endif
  }
  else
  {
#ifdef HAVE_NCURSES
    if(options->expert>0 &&
	ask_confirmation("Try to unformat a FAT filesystem (Y/N)")!=0)
      params->status=STATUS_UNFORMAT;
#endif
  }
  /*@ assert valid_read_string(params->recup_dir); */
  screen_buffer_reset();
#ifndef DISABLED_FOR_FRAMAC
  log_info("\nAnalyse\n");
  log_partition(params->disk, params->partition);
#endif
  /*@ assert valid_read_string(params->recup_dir); */
  /* make the first recup_dir */
  params->dir_num=photorec_mkdir(params->recup_dir, params->dir_num);

#ifdef ENABLE_DFXML
  /* Open the XML output file */
  xml_open(params->recup_dir, params->dir_num);
  xml_setup(params->disk, params->partition);
#endif
  
  /*@
    @ loop invariant valid_ph_param(params);
    @*/
  for(params->pass=0; params->status!=STATUS_QUIT; params->pass++)
  {
    const unsigned int old_file_nbr=params->file_nbr;
#ifndef DISABLED_FOR_FRAMAC
    log_info("Pass %u (blocksize=%u) ", params->pass, params->blocksize);
    log_info("%s\n", status_to_name(params->status));
#endif

#ifdef HAVE_NCURSES
    aff_copy(stdscr);
    wmove(stdscr, 4, 0);
    wprintw(stdscr, "%s", params->disk->description_short(params->disk));
    mvwaddstr(stdscr, 5, 0, msg_PART_HEADER_LONG);
    wmove(stdscr, 6, 0);
    aff_part(stdscr, AFF_PART_ORDER|AFF_PART_STATUS, params->disk, params->partition);
    wmove(stdscr, 22, 0);
    wattrset(stdscr, A_REVERSE);
    waddstr(stdscr, "  Stop  ");
    wattroff(stdscr, A_REVERSE);
    wrefresh(stdscr);
#endif
    switch(params->status)
    {
      case STATUS_UNFORMAT:
#ifndef DISABLED_FOR_FRAMAC
	ind_stop=fat_unformat(params, options, list_search_space);
#endif
	params->blocksize=blocksize_is_known;
	break;
      case STATUS_FIND_OFFSET:
#ifndef DISABLED_FOR_FRAMAC
	{
	  uint64_t start_offset=0;
	  if(blocksize_is_known>0)
	  {
	    ind_stop=PSTATUS_OK;
	    if(!td_list_empty(&list_search_space->list))
	      start_offset=(td_list_first_entry(&list_search_space->list, alloc_data_t, list))->start % params->blocksize;
	  }
	  else
	  {
	    ind_stop=photorec_find_blocksize(params, options, list_search_space);
	    params->blocksize=find_blocksize(list_search_space, params->disk->sector_size, &start_offset);
	  }
#ifdef HAVE_NCURSES
	  if(options->expert>0)
	    menu_choose_blocksize(&params->blocksize, &start_offset, params->disk->sector_size);
#endif
	  update_blocksize(params->blocksize, list_search_space, start_offset);
	}
#else
	params->blocksize=512;
#endif
	break;
      case STATUS_EXT2_ON_BF:
      case STATUS_EXT2_OFF_BF:
#ifndef DISABLED_FOR_FRAMAC
	ind_stop=photorec_bf(params, options, list_search_space);
#endif
	break;
      default:
	ind_stop=photorec_aux(params, options, list_search_space);
	break;
    }
    session_save(list_search_space, params, options);
    if(need_to_stop!=0)
      ind_stop=PSTATUS_STOP;
    switch(ind_stop)
    {
      case PSTATUS_ENOSPC:
	{ /* no more space */
#ifdef HAVE_NCURSES
	  char dst_directory[4096];
	  char *res;
	  strncpy(dst_directory, params->recup_dir, sizeof(dst_directory)-1);
	  dst_directory[4095]='\0';
	  res=strrchr(dst_directory, '/');
	  if(res!=NULL)
	    *res='\0';
	  ask_location(dst_directory, sizeof(dst_directory), "Warning: not enough free space available. Please select a destination to save the recovered files to.\nDo not choose to write the files to the same partition they were stored on.", "");
	  if(dst_directory[0]=='\0')
	    params->status=STATUS_QUIT;
	  else
	  {
	    free(params->recup_dir);
	    params->recup_dir=(char *)MALLOC(strlen(dst_directory)+1+strlen(DEFAULT_RECUP_DIR)+1);
	    strcpy(params->recup_dir, dst_directory);
	    if(strcmp(params->recup_dir,"/")!=0)
	      strcat(params->recup_dir,"/");
	    strcat(params->recup_dir,DEFAULT_RECUP_DIR);
	    /* Create the directory */
	    params->dir_num=photorec_mkdir(params->recup_dir,params->dir_num);
	  }
#else
	  params->status=STATUS_QUIT;
#endif
	}
	break;
      case PSTATUS_EACCES:
	if(interface_cannot_create_file()!=0)
	  params->status=STATUS_QUIT;
	break;
      case PSTATUS_STOP:
	if(session_save(list_search_space, params, options) < 0)
	{
	  /* Failed to save the session! */
#ifdef HAVE_NCURSES
	  if(ask_confirmation("PhotoRec has been unable to save its session status. Answer Y to really Quit, N to resume the recovery")!=0)
#endif
	    params->status=STATUS_QUIT;
	}
	else
	{
	  log_flush();
#ifdef HAVE_NCURSES
	  if(need_to_stop!=0 || ask_confirmation("Answer Y to really Quit, N to resume the recovery")!=0)
#endif
	    params->status=STATUS_QUIT;
	}
	break;
      case PSTATUS_OK:
	status_inc(params, options);
	if(params->status==STATUS_QUIT)
	  unlink("photorec.ses");
	break;
    }
#ifndef DISABLED_FOR_FRAMAC
    {
      const time_t current_time=time(NULL);
      log_info("Elapsed time %uh%02um%02us\n",
          (unsigned)((current_time-params->real_start_time)/60/60),
          (unsigned)((current_time-params->real_start_time)/60%60),
          (unsigned)((current_time-params->real_start_time)%60));
    }
    update_stats(params->file_stats, list_search_space);
    if(params->pass>0)
    {
      log_info("Pass %u +%u file%s\n",params->pass,params->file_nbr-old_file_nbr,(params->file_nbr-old_file_nbr<=1?"":"s"));
      write_stats_log(params->file_stats);
      json_log_progress(params, params->pass, params->offset);
    }
    log_flush();
#endif
  }
#ifdef HAVE_NCURSES
  if(options->expert>0 && !td_list_empty(&list_search_space->list))
  {
    char msg[256];
    uint64_t data_size=0;
    struct td_list_head *search_walker = NULL;
    td_list_for_each(search_walker, &list_search_space->list)
    {
      const alloc_data_t *current_search_space;
      current_search_space=td_list_entry(search_walker, alloc_data_t, list);
      data_size += current_search_space->end - current_search_space->start + 1;
    }
    snprintf(msg, sizeof(msg),
	"Create an image_remaining.dd (%u MB) file with the unknown data (Answer N if not sure) (Y/N)",
	(unsigned int)(data_size/1000/1000));
    if(ask_confirmation("%s", msg)!=0)
    {
      char *filename;
      char *res;
      char *dst_path=strdup(params->recup_dir);
      res=strrchr(dst_path, '/');
      if(res!=NULL)
	*res='\0';
      else
      {
	dst_path[0]='.';
	dst_path[1]='\0';
      }
      filename=(char *)MALLOC(strlen(dst_path) + 1 + strlen(DEFAULT_IMAGE_NAME) + 1);
      strcpy(filename, dst_path);
      if(strcmp(params->recup_dir,"/")!=0)
	strcat(filename, "/");
      strcat(filename, DEFAULT_IMAGE_NAME);
      gen_image(filename, params->disk, list_search_space);
      free(filename);
      free(dst_path);
    }
  }
#endif
  info_list_search_space(list_search_space, NULL, params->disk->sector_size, options->keep_corrupted_file, options->verbose);
  /* Free memory */
  free_search_space(list_search_space);
#ifdef HAVE_NCURSES
  if(params->cmd_run==NULL)
    recovery_finished(params->disk, params->partition, params->file_nbr, params->recup_dir, ind_stop);
#endif
  json_log_completion(params, "PhotoRec completed recovery");
  free(params->file_stats);
  params->file_stats=NULL;
  free_header_check();
#ifdef ENABLE_DFXML
  xml_shutdown();
  xml_close();
#endif
  return 0;
}

#ifdef HAVE_NCURSES
static void format_filesize_input(uint64_t size, char *buffer, size_t buffer_size)
{
  if(size == 0)
  {
    buffer[0] = '\0';
    return;
  }

  if(size >= 1024ULL*1024ULL*1024ULL*1024ULL)
  {
    double tb = (double)size / (1024ULL*1024ULL*1024ULL*1024ULL);
    snprintf(buffer, buffer_size, "%.2ft", tb);
  }
  else if(size >= 1024*1024*1024)
  {
    double gb = (double)size / (1024*1024*1024);
    snprintf(buffer, buffer_size, "%.2fg", gb);
  }
  else if(size >= 1024*1024)
  {
    double mb = (double)size / (1024*1024);
    snprintf(buffer, buffer_size, "%.2fm", mb);
  }
  else if(size >= 1024)
  {
    double kb = (double)size / 1024.0;
    snprintf(buffer, buffer_size, "%.2fk", kb);
  }
  else
  {
    snprintf(buffer, buffer_size, "%lu", (unsigned long)size);
  }
}

/* Forward declarations */
static void interface_edit_filesize_field(file_size_filter_t *filter, int field_num);
static void interface_filesize_photorec_ncurses(struct ph_options *options);

void interface_options_photorec_ncurses(struct ph_options *options)
{
  unsigned int menu = 7;
  struct MenuItem menuOptions[]=
  {
    { 'P', NULL, "Check JPG files" },
    { 'K',NULL,"Keep corrupted files"},
    { 'S',NULL,"Try to skip indirect block"},
    { 'E',NULL,"Provide additional controls"},
    { 'L',NULL,"Low memory"},
    { 'M',NULL,"File size filter"},
    { 'I',NULL,"Image size filters"},
    { 'Q',"Quit","Return to main menu"},
    { 0, NULL, NULL }
  };
  while (1)
  {
    int car;
    int real_key;
    switch(options->paranoid)
    {
      case 0:
	menuOptions[0].name="Paranoid : No";
	break;
      case 1:
	menuOptions[0].name="Paranoid : Yes (Brute force disabled)";
	break;
      default:
	menuOptions[0].name="Paranoid : Yes (Brute force enabled)";
	break;
    }
    menuOptions[1].name=options->keep_corrupted_file?"Keep corrupted files : Yes":"Keep corrupted files : No";
    menuOptions[2].name=options->mode_ext2?"ext2/ext3 mode: Yes":"ext2/ext3 mode : No";
    menuOptions[3].name=options->expert?"Expert mode : Yes":"Expert mode : No";
    menuOptions[4].name=options->lowmem?"Low memory: Yes":"Low memory: No";
    {
      static char filesize_str[128];
      if(options->file_size_filter.min_file_size > 0 || options->file_size_filter.max_file_size > 0)
      {
        char min_str[32], max_str[32];
        format_filesize_input(options->file_size_filter.min_file_size, min_str, sizeof(min_str));
        format_filesize_input(options->file_size_filter.max_file_size, max_str, sizeof(max_str));
        snprintf(filesize_str, sizeof(filesize_str), "File size : %s-%s",
          strlen(min_str) > 0 ? min_str : "",
          strlen(max_str) > 0 ? max_str : "");
      }
      else
        snprintf(filesize_str, sizeof(filesize_str), "File size : No limit");
      menuOptions[5].name=filesize_str;
    }
    menuOptions[6].name=has_any_image_size_filter(&options->image_filter)?"Image size filters : Enabled":"Image size filters : Disabled";
    aff_copy(stdscr);
    car=wmenuSelect_ext(stdscr, 23, INTER_OPTION_Y, INTER_OPTION_X, menuOptions, 0, "PKELMIQ", MENU_VERT|MENU_VERT_ARROW2VALID, &menu,&real_key);
    switch(car)
    {
      case 'p':
      case 'P':
	if(options->paranoid<2)
	  options->paranoid++;
	else
	  options->paranoid=0;
	break;
      case 'k':
      case 'K':
	options->keep_corrupted_file=!options->keep_corrupted_file;
	break;
      case 's':
      case 'S':
	options->mode_ext2=!options->mode_ext2;
	break;
      case 'e':
      case 'E':
	options->expert=!options->expert;
	break;
      case 'l':
      case 'L':
	options->lowmem=!options->lowmem;
	break;
      case 'm':
      case 'M':
	interface_filesize_photorec_ncurses(options);
	break;
      case 'i':
      case 'I':
	interface_imagesize_photorec_ncurses(options);
	break;
      case key_ESC:
      case 'q':
      case 'Q':
	interface_options_photorec_log(options);
	return;
    }
  }
}

#define INTER_FSELECT_X	0
#define INTER_FSELECT_Y	(LINES-2)
#define INTER_FSELECT	(LINES-10)

typedef struct {
  const char *name;
  const char *keywords[20];
} file_category_t;

static const file_category_t file_categories[] = {
  {"Images", {"picture", "image", "photo", "icon", "bitmap", "graphics", NULL}},
  {"RAW Images", {"raw", NULL}},
  {"Videos", {"video", "movie", "film", NULL}},
  {"Audio", {"audio", "sound", "music", "midi", NULL}},
  {"Documents", {"document", "spreadsheet", "presentation", "text", "word", "excel", "powerpoint", NULL}},
  {"Archives", {"archive", "compressed", "compression", "zip", NULL}},
  {"Databases", {"database", NULL}},
  {NULL, {NULL}}
};

static int is_file_in_category(const file_hint_t *file_hint, const file_category_t *category)
{
  int i;
  if(file_hint == NULL || category == NULL || file_hint->description == NULL)
    return 0;

  /* Special case: if category is "RAW Images", exclude files with "video" or "audio" in description */
  if(strcmp(category->name, "RAW Images") == 0)
  {
    if(strcasestr(file_hint->description, "video") != NULL ||
       strcasestr(file_hint->description, "audio") != NULL ||
       strcasestr(file_hint->description, "movie") != NULL)
      return 0;
  }

  /* Convert description to lowercase for case-insensitive comparison */
  for(i = 0; category->keywords[i] != NULL; i++)
  {
    if(strcasestr(file_hint->description, category->keywords[i]) != NULL)
      return 1;
  }
  return 0;
}

static void select_file_category_ncurses(file_enable_t *files_enable)
{
  int current = 0;
  int done = 0;

  while(!done)
  {
    int i, command;
    int category_count = 0;

    /* Count categories */
    for(i = 0; file_categories[i].name != NULL; i++)
      category_count++;

    aff_copy(stdscr);
    wmove(stdscr, 4, 0);
    wprintw(stdscr, "Select file type category to enable:");

    /* Display categories */
    for(i = 0; file_categories[i].name != NULL; i++)
    {
      wmove(stdscr, 6 + i, 0);
      if(i == current)
        wattrset(stdscr, A_REVERSE);
      wprintw(stdscr, " %s ", file_categories[i].name);
      if(i == current)
        wattroff(stdscr, A_REVERSE);
    }

    /* Display help */
    wmove(stdscr, 6 + category_count + 1, 0);
    wprintw(stdscr, "Press Enter to select category, q to quit");

    wrefresh(stdscr);
    command = wgetch(stdscr);

    switch(command)
    {
      case KEY_UP:
      case '8':
        if(current > 0)
          current--;
        break;
      case KEY_DOWN:
      case '2':
        if(current < category_count - 1)
          current++;
        break;
      case '\r':
      case '\n':
      case KEY_ENTER:
        {
          file_enable_t *file_enable;
          const file_category_t *selected_category = &file_categories[current];
          /* Enable all files in selected category */
          for(file_enable = &files_enable[0]; file_enable->file_hint != NULL; file_enable++)
          {
            if(is_file_in_category(file_enable->file_hint, selected_category))
            {
              file_enable->enable = 1;
            }
          }
          done = 1;
        }
        break;
      case 'q':
      case 'Q':
      case 27: /* ESC */
        done = 1;
        break;
    }
  }
}

void interface_file_select_ncurses(file_enable_t *files_enable)
{
  int current_element_num=0;
  int offset=0;
  int old_LINES=0;	/* Screen will be cleared */
  unsigned int menu=0;
  int enable_status=files_enable[0].enable;
  char search_filter[256]="";
  int search_mode=0;
  int can_restore=file_options_exists();
  static const struct MenuItem menuAdv[]=
  {
    {'q',"Quit","Return to main menu"},
    {0,NULL,NULL}
  };
  log_info("\nInterface File Select\n");
  while(1)
  {
    int i;
    int command;
    int total_count=0;
    int selected_count=0;
    int filtered_count=0;
    int items_before=0;
    int items_after=0;
    int display_idx;
    int current_display_idx=-1;
    int first_visible_line=6;
    int displayed_count=0;

    /* Count total, selected, and filtered items */
    for(i=0; files_enable[i].file_hint!=NULL; i++)
    {
      int matches=1;
      total_count++;
      if(files_enable[i].enable)
        selected_count++;

      if(search_filter[0]!='\0')
      {
        const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
        const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
        char combined[512];
        snprintf(combined, sizeof(combined), "%s %s", ext, desc);
        matches = (strcasestr(combined, search_filter) != NULL);
      }

      if(matches)
        filtered_count++;
    }

    if(old_LINES!=LINES)
    {
      aff_copy(stdscr);
      current_element_num=0;
      offset=0;
      old_LINES=LINES;
    }

    /* Display header with counts */
    wmove(stdscr,4,0);
    wclrtoeol(stdscr);
    wprintw(stdscr,"PhotoRec will try to locate the following files [%d/%d selected]", selected_count, total_count);

    /* Display search info if active */
    wmove(stdscr,5,0);
    wclrtoeol(stdscr);
    if(search_filter[0]!='\0')
    {
      wprintw(stdscr,"Filter: %s [%d/%d matches]", search_filter, filtered_count, total_count);
    }
    else if(search_mode)
    {
      wprintw(stdscr,"Filter: ");
    }

    /* Clear line 6 - will be used for "above" message or first file entry */
    wmove(stdscr,6,0);
    wclrtoeol(stdscr);

    /* Display file list with filter applied */
    display_idx=0;
    current_display_idx=-1;
    first_visible_line=6;

    /* Count items before viewport for "above" message */
    for(i=0; files_enable[i].file_hint!=NULL; i++)
    {
      int matches=1;
      if(search_filter[0]!='\0')
      {
        const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
        const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
        char combined[512];
        snprintf(combined, sizeof(combined), "%s %s", ext, desc);
        matches = (strcasestr(combined, search_filter) != NULL);
      }
      if(!matches)
        continue;
      if(display_idx < offset)
        items_before++;
      display_idx++;
    }

    /* Calculate current_display_idx and adjust offset BEFORE displaying */
    current_display_idx=-1;
    display_idx=0;
    for(i=0; files_enable[i].file_hint!=NULL; i++)
    {
      int matches=1;
      if(search_filter[0]!='\0')
      {
        const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
        const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
        char combined[512];
        snprintf(combined, sizeof(combined), "%s %s", ext, desc);
        matches = (strcasestr(combined, search_filter) != NULL);
      }
      if(!matches)
        continue;
      if(i==current_element_num)
        current_display_idx=display_idx;
      display_idx++;
    }

    /* Adjust offset to keep current element visible */
    /* Strategy: scroll by INTER_FSELECT-1 so that when "above" message appears, it fits */
    if(current_display_idx>=0)
    {
      if(current_display_idx<offset)
        offset=current_display_idx;
      if(current_display_idx>=offset+INTER_FSELECT-1)
        offset=current_display_idx-(INTER_FSELECT-1)+1;
    }

    /* Recalculate items_before after offset adjustment */
    items_before=0;
    display_idx=0;
    for(i=0; files_enable[i].file_hint!=NULL; i++)
    {
      int matches=1;
      if(search_filter[0]!='\0')
      {
        const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
        const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
        char combined[512];
        snprintf(combined, sizeof(combined), "%s %s", ext, desc);
        matches = (strcasestr(combined, search_filter) != NULL);
      }
      if(!matches)
        continue;
      if(display_idx < offset)
        items_before++;
      display_idx++;
    }

    /* Display "above" message if needed */
    if(items_before>0)
    {
      wmove(stdscr,6,0);
      wattrset(stdscr, A_DIM);
      wprintw(stdscr,"%d more item%s above", items_before, items_before>1?"s":"");
      wattroff(stdscr, A_DIM);
      first_visible_line=7;
    }

    /* Now display the actual list */
    display_idx=0;
    items_before=0;
    items_after=0;
    displayed_count=0;
    {
      int max_visible = INTER_FSELECT;
      if(first_visible_line==7)
        max_visible = INTER_FSELECT - 1;

      for(i=0; files_enable[i].file_hint!=NULL; i++)
      {
        int matches=1;

        if(search_filter[0]!='\0')
        {
          const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
          const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
          char combined[512];
          snprintf(combined, sizeof(combined), "%s %s", ext, desc);
          matches = (strcasestr(combined, search_filter) != NULL);
        }

        if(!matches)
          continue;

        if(i==current_element_num)
          current_display_idx=display_idx;

        if(display_idx < offset)
        {
          display_idx++;
          continue;
        }

        if(displayed_count >= max_visible)
        {
          items_after++;
          display_idx++;
          continue;
        }

        wmove(stdscr,first_visible_line+displayed_count,0);
        wclrtoeol(stdscr);
        if(i==current_element_num)
        {
          wattrset(stdscr, A_REVERSE);
          wprintw(stdscr,">[%c] %-4s %s", (files_enable[i].enable==0?' ':'X'),
              (files_enable[i].file_hint->extension!=NULL?
               files_enable[i].file_hint->extension:""),
              files_enable[i].file_hint->description);
          wattroff(stdscr, A_REVERSE);
        }
        else
        {
          wprintw(stdscr," [%c] %-4s %s", (files_enable[i].enable==0?' ':'X'),
              (files_enable[i].file_hint->extension!=NULL?
               files_enable[i].file_hint->extension:""),
              files_enable[i].file_hint->description);
        }
        displayed_count++;
        display_idx++;
      }
    }

    /* Clear remaining lines in display area */
    {
      int max_visible = INTER_FSELECT;
      if(first_visible_line==7)
        max_visible = INTER_FSELECT - 1;
      for(i=displayed_count; i<max_visible; i++)
      {
        wmove(stdscr,first_visible_line+i,0);
        wclrtoeol(stdscr);
      }
    }

    /* Clear and display count of items outside viewport at bottom */
    /* "below" message always on line 6+INTER_FSELECT, menu always on 6+INTER_FSELECT+1 */
    wmove(stdscr,6+INTER_FSELECT,0);
    wclrtoeol(stdscr);
    if(items_after>0)
    {
      wattrset(stdscr, A_DIM);
      wprintw(stdscr,"%d more item%s below", items_after, items_after>1?"s":"");
      wattroff(stdscr, A_DIM);
    }

    wmove(stdscr,6+INTER_FSELECT+1,0);
    wclrtoeol(stdscr);
    wprintw(stdscr,"Press ");
    if(has_colors())
      wbkgdset(stdscr,' ' | A_BOLD | COLOR_PAIR(0));
    wprintw(stdscr,"f");
    if(has_colors())
      wbkgdset(stdscr,' ' | COLOR_PAIR(0));
    wprintw(stdscr," filter, ");
    if(has_colors())
      wbkgdset(stdscr,' ' | A_BOLD | COLOR_PAIR(0));
    wprintw(stdscr,"s");
    if(has_colors())
      wbkgdset(stdscr,' ' | COLOR_PAIR(0));
    if(enable_status==0)
      wprintw(stdscr," select all, ");
    else
      wprintw(stdscr," clear all, ");
    if(has_colors())
      wbkgdset(stdscr,' ' | A_BOLD | COLOR_PAIR(0));
    wprintw(stdscr,"i");
    if(has_colors())
      wbkgdset(stdscr,' ' | COLOR_PAIR(0));
    wprintw(stdscr," invert, ");
    if(has_colors())
      wbkgdset(stdscr,' ' | A_BOLD | COLOR_PAIR(0));
    wprintw(stdscr,"t");
    if(has_colors())
      wbkgdset(stdscr,' ' | COLOR_PAIR(0));
    wprintw(stdscr," select type, ");
    if(can_restore)
    {
      if(has_colors())
        wbkgdset(stdscr,' ' | A_BOLD | COLOR_PAIR(0));
      wprintw(stdscr,"r");
      if(has_colors())
        wbkgdset(stdscr,' ' | COLOR_PAIR(0));
      wprintw(stdscr," restore, ");
    }
    else
    {
      wattrset(stdscr, A_DIM);
      wprintw(stdscr,"r restore, ");
      wattroff(stdscr, A_DIM);
    }
    if(has_colors())
      wbkgdset(stdscr,' ' | A_BOLD | COLOR_PAIR(0));
    wprintw(stdscr,"b");
    if(has_colors())
      wbkgdset(stdscr,' ' | COLOR_PAIR(0));
    wprintw(stdscr," save");

    if(search_mode)
    {
      int ch;
      wmove(stdscr,5,8+strlen(search_filter));
      wrefresh(stdscr);
      ch = wgetch(stdscr);
      if(ch=='\n' || ch=='\r' || ch==KEY_ENTER)
      {
        search_mode=0;
        /* Find first matching element after exiting search mode */
        if(search_filter[0]!='\0')
        {
          int found=0;
          for(i=0; files_enable[i].file_hint!=NULL && !found; i++)
          {
            const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
            const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
            char combined[512];
            snprintf(combined, sizeof(combined), "%s %s", ext, desc);
            if(strcasestr(combined, search_filter) != NULL)
            {
              current_element_num=i;
              offset=0;
              found=1;
            }
          }
        }
      }
      else if(ch==27) /* ESC */
      {
        search_filter[0]='\0';
        search_mode=0;
        current_element_num=0;
      }
      else if(ch==KEY_BACKSPACE || ch==127 || ch==8)
      {
        int len=strlen(search_filter);
        if(len>0)
        {
          search_filter[len-1]='\0';
          /* After removing character, find first matching element */
          if(search_filter[0]!='\0')
          {
            int found=0;
            for(i=0; files_enable[i].file_hint!=NULL && !found; i++)
            {
              const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
              const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
              char combined[512];
              snprintf(combined, sizeof(combined), "%s %s", ext, desc);
              if(strcasestr(combined, search_filter) != NULL)
              {
                current_element_num=i;
                offset=0;
                found=1;
              }
            }
          }
          else
          {
            current_element_num=0;
            offset=0;
          }
        }
      }
      else if(((ch>='a' && ch<='z') || (ch>='A' && ch<='Z') || (ch>='0' && ch<='9')) && strlen(search_filter)<sizeof(search_filter)-1)
      {
        int len=strlen(search_filter);
        search_filter[len]=ch;
        search_filter[len+1]='\0';
        /* After adding character, find first matching element */
        if(search_filter[0]!='\0')
        {
          int found=0;
          for(i=0; files_enable[i].file_hint!=NULL && !found; i++)
          {
            const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
            const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
            char combined[512];
            snprintf(combined, sizeof(combined), "%s %s", ext, desc);
            if(strcasestr(combined, search_filter) != NULL)
            {
              current_element_num=i;
              offset=0;
              found=1;
            }
          }
        }
      }
      continue;
    }

    wrefresh(stdscr);
    command = wmenuSelect(stdscr, LINES-1, INTER_FSELECT_Y, INTER_FSELECT_X, menuAdv, 8,
	"q", MENU_BUTTON | MENU_ACCEPT_OTHERS, menu);

    switch(command)
    {
      case 27: /* ESC - clear filter */
        if(search_filter[0]!='\0')
        {
          search_filter[0]='\0';
          current_element_num=0;
          offset=0;
        }
        break;
      case 'f':
      case 'F':
        search_mode=1;
        break;
      case KEY_UP:
      case '8':
	{
	  int found=0;
	  for(i=current_element_num-1; i>=0 && !found; i--)
	  {
	    int matches=1;
	    if(search_filter[0]!='\0')
	    {
	      const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
	      const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
	      char combined[512];
	      snprintf(combined, sizeof(combined), "%s %s", ext, desc);
	      matches = (strcasestr(combined, search_filter) != NULL);
	    }
	    if(matches)
	    {
	      current_element_num=i;
	      found=1;
	    }
	  }
	}
	break;
      case KEY_PPAGE:
      case '9':
	for(i=0; i<INTER_FSELECT-1; i++)
	{
	  int found=0;
	  int j;
	  for(j=current_element_num-1; j>=0 && !found; j--)
	  {
	    int matches=1;
	    if(search_filter[0]!='\0')
	    {
	      const char *ext = files_enable[j].file_hint->extension ? files_enable[j].file_hint->extension : "";
	      const char *desc = files_enable[j].file_hint->description ? files_enable[j].file_hint->description : "";
	      char combined[512];
	      snprintf(combined, sizeof(combined), "%s %s", ext, desc);
	      matches = (strcasestr(combined, search_filter) != NULL);
	    }
	    if(matches)
	    {
	      current_element_num=j;
	      found=1;
	    }
	  }
	  if(!found)
	    break;
	}
	break;
      case KEY_DOWN:
      case '2':
	{
	  int found=0;
	  for(i=current_element_num+1; files_enable[i].file_hint!=NULL && !found; i++)
	  {
	    int matches=1;
	    if(search_filter[0]!='\0')
	    {
	      const char *ext = files_enable[i].file_hint->extension ? files_enable[i].file_hint->extension : "";
	      const char *desc = files_enable[i].file_hint->description ? files_enable[i].file_hint->description : "";
	      char combined[512];
	      snprintf(combined, sizeof(combined), "%s %s", ext, desc);
	      matches = (strcasestr(combined, search_filter) != NULL);
	    }
	    if(matches)
	    {
	      current_element_num=i;
	      found=1;
	    }
	  }
	}
	break;
      case KEY_NPAGE:
      case '3':
	for(i=0; i<INTER_FSELECT-1; i++)
	{
	  int found=0;
	  int j;
	  for(j=current_element_num+1; files_enable[j].file_hint!=NULL && !found; j++)
	  {
	    int matches=1;
	    if(search_filter[0]!='\0')
	    {
	      const char *ext = files_enable[j].file_hint->extension ? files_enable[j].file_hint->extension : "";
	      const char *desc = files_enable[j].file_hint->description ? files_enable[j].file_hint->description : "";
	      char combined[512];
	      snprintf(combined, sizeof(combined), "%s %s", ext, desc);
	      matches = (strcasestr(combined, search_filter) != NULL);
	    }
	    if(matches)
	    {
	      current_element_num=j;
	      found=1;
	    }
	  }
	  if(!found)
	    break;
	}
	break;
      case KEY_RIGHT:
      case '+':
      case ' ':
      case KEY_LEFT:
      case '-':
      case 'x':
      case 'X':
      case '4':
      case '5':
      case '6':
	files_enable[current_element_num].enable=1-files_enable[current_element_num].enable;
	break;
      case 's':
      case 'S':
	{
	  file_enable_t *file_enable;
	  if(enable_status==0)
	  {
	    /* Currently showing "select all", so select all files */
	    for(file_enable=&files_enable[0];file_enable->file_hint!=NULL;file_enable++)
	      file_enable->enable=1;
	  }
	  else
	  {
	    /* Currently showing "clear all", so clear all files */
	    for(file_enable=&files_enable[0];file_enable->file_hint!=NULL;file_enable++)
	      file_enable->enable=0;
	  }
	  enable_status=1-enable_status;
	}
	break;
      case 'i':
      case 'I':
	{
	  file_enable_t *file_enable;
	  for(file_enable=&files_enable[0];file_enable->file_hint!=NULL;file_enable++)
	    file_enable->enable=1-file_enable->enable;
	}
	break;
      case 't':
      case 'T':
	select_file_category_ncurses(files_enable);
	break;
      case 'r':
      case 'R':
	if(can_restore)
	{
	  if(file_options_load(files_enable)<0)
	  {
	    display_message("Failed to restore the settings.");
	  }
	  else
	  {
	    display_message("Settings restored successfully.");
	    can_restore=file_options_exists();
	  }
	}
	break;
      case 'b':
      case 'B':
	if(selected_count==0)
	{
	  display_message("Please select at least one file type before saving.");
	}
	else if(file_options_save(files_enable)<0)
	{
	  display_message("Failed to save the settings.");
	}
	else
	{
	  display_message("Settings recorded successfully.");
	  can_restore=1;
	}
	break;
      case 'q':
      case 'Q':
	if(selected_count==0)
	{
	  display_message("Please select at least one file type before continuing.");
	}
	else
	{
	  return;
	}
    }
  }
}

static void interface_edit_image_filter_field(image_size_filter_t *filter, int field_num)
{
  char input[32];
  char prompt[64];
  char current_value[32] = "";

  /* Prepare current value and prompt */
  switch(field_num) {
    case 1: /* width min */
      if (filter->min_width > 0) {
        snprintf(current_value, sizeof(current_value), "%u", filter->min_width);
      }
      snprintf(prompt, sizeof(prompt), "Min width (pixels): ");
      break;
    case 2: /* width max */
      if (filter->max_width > 0) {
        snprintf(current_value, sizeof(current_value), "%u", filter->max_width);
      }
      snprintf(prompt, sizeof(prompt), "Max width (pixels): ");
      break;
    case 3: /* height min */
      if (filter->min_height > 0) {
        snprintf(current_value, sizeof(current_value), "%u", filter->min_height);
      }
      snprintf(prompt, sizeof(prompt), "Min height (pixels): ");
      break;
    case 4: /* height max */
      if (filter->max_height > 0) {
        snprintf(current_value, sizeof(current_value), "%u", filter->max_height);
      }
      snprintf(prompt, sizeof(prompt), "Max height (pixels): ");
      break;
    case 5: /* pixels min */
      if (filter->min_pixels > 0) {
        if (strlen(pixels_min_format) > 0) {
          snprintf(current_value, sizeof(current_value), "%s", pixels_min_format);
        } else {
          snprintf(current_value, sizeof(current_value), "%lu", (unsigned long)filter->min_pixels);
        }
      }
      snprintf(prompt, sizeof(prompt), "Min pixels (total or WIDTHxHEIGHT): ");
      break;
    case 6: /* pixels max */
      if (filter->max_pixels > 0) {
        if (strlen(pixels_max_format) > 0) {
          snprintf(current_value, sizeof(current_value), "%s", pixels_max_format);
        } else {
          snprintf(current_value, sizeof(current_value), "%lu", (unsigned long)filter->max_pixels);
        }
      }
      snprintf(prompt, sizeof(prompt), "Max pixels (total or WIDTHxHEIGHT): ");
      break;
    default:
      return;
  }

  /* Show input dialog */
  aff_copy(stdscr);
  wmove(stdscr, LINES/2-1, 0);
  wprintw(stdscr, "%s", prompt);
  wmove(stdscr, LINES/2, 0);
  wprintw(stdscr, "Current: %s", strlen(current_value) > 0 ? current_value : "none");
  wmove(stdscr, LINES/2+1, 0);
  wprintw(stdscr, "New value (empty to clear, Esc to cancel): ");
  wrefresh(stdscr);

  /* Get input with Escape support */
  int ch;
  int input_pos = 0;
  int prompt_len = 44; /* Length of "New value (empty to clear, Esc to cancel): " */
  input[0] = '\0';

  /* Position cursor right after the prompt */
  wmove(stdscr, LINES/2+1, prompt_len);
  wrefresh(stdscr);

  echo();
  while (1) {
    ch = wgetch(stdscr);

    if (ch == key_ESC) {
      noecho();
      return; /* Cancel - don't change anything */
    }
    else if (ch == '\n' || ch == '\r') {
      break; /* Enter pressed - accept input (even if empty) */
    }
    else if (ch == KEY_BACKSPACE || ch == 127 || ch == 8) {
      if (input_pos > 0) {
        input_pos--;
        input[input_pos] = '\0';
        /* Move cursor back and clear character */
        wmove(stdscr, LINES/2+1, prompt_len + input_pos);
        waddch(stdscr, ' ');
        wmove(stdscr, LINES/2+1, prompt_len + input_pos);
        wrefresh(stdscr);
      }
    }
    else if (ch >= 32 && ch <= 126 && input_pos < sizeof(input)-2) { /* Printable characters */
      input[input_pos] = ch;
      input_pos++;
      input[input_pos] = '\0';
      /* Position cursor and add character */
      wmove(stdscr, LINES/2+1, prompt_len + input_pos - 1);
      waddch(stdscr, ch);
      wrefresh(stdscr);
    }
  }
  noecho();

  /* Parse and apply input */
  if (strlen(input) > 0) {
    switch(field_num) {
      case 1: /* width min */
        {
          char *ptr = input;
          uint64_t val = (uint64_t)get_int_from_command(&ptr);
          if (val > UINT32_MAX) {
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Width must be <= %u", UINT32_MAX);
            wrefresh(stdscr);
            wgetch(stdscr);
            return;
          }
          filter->min_width = (uint32_t)val;
        }
        /* Clear pixels min when setting width min */
        filter->min_pixels = 0;
        /* Clear saved format */
        pixels_min_format[0] = '\0';
        break;
      case 2: /* width max */
        {
          char *ptr = input;
          uint64_t val = (uint64_t)get_int_from_command(&ptr);
          if (val > UINT32_MAX) {
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Width must be <= %u", UINT32_MAX);
            wrefresh(stdscr);
            wgetch(stdscr);
            return;
          }
          filter->max_width = (uint32_t)val;
        }
        /* Clear pixels max when setting width max */
        filter->max_pixels = 0;
        /* Clear saved format */
        pixels_max_format[0] = '\0';
        break;
      case 3: /* height min */
        {
          char *ptr = input;
          uint64_t val = (uint64_t)get_int_from_command(&ptr);
          if (val > UINT32_MAX) {
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Height must be <= %u", UINT32_MAX);
            wrefresh(stdscr);
            wgetch(stdscr);
            return;
          }
          filter->min_height = (uint32_t)val;
        }
        /* Clear pixels min when setting height min */
        filter->min_pixels = 0;
        /* Clear saved format */
        pixels_min_format[0] = '\0';
        break;
      case 4: /* height max */
        {
          char *ptr = input;
          uint64_t val = (uint64_t)get_int_from_command(&ptr);
          if (val > UINT32_MAX) {
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Height must be <= %u", UINT32_MAX);
            wrefresh(stdscr);
            wgetch(stdscr);
            return;
          }
          filter->max_height = (uint32_t)val;
        }
        /* Clear pixels max when setting height max */
        filter->max_pixels = 0;
        /* Clear saved format */
        pixels_max_format[0] = '\0';
        break;
      case 5: /* pixels min */
        /* Check string length first to prevent buffer overflows */
        if (strlen(input) > 31) {
          aff_copy(stdscr);
          wmove(stdscr, LINES/2, 0);
          wprintw(stdscr, "Error: Input too long");
          wrefresh(stdscr);
          wgetch(stdscr);
          return;
        }

        /* Check if it's WIDTHxHEIGHT format */
        if(strchr(input, 'x') != NULL) {
          uint64_t width = 0, height = 0;
          char *ptr = input;

          /* Parse width with overflow check */
          while(*ptr && isdigit(*ptr)) {
            if (width > UINT64_MAX / 10) {
              aff_copy(stdscr);
              wmove(stdscr, LINES/2, 0);
              wprintw(stdscr, "Error: Width value too large");
              wrefresh(stdscr);
              wgetch(stdscr);
              return;
            }
            width = width * 10;
            if (width > UINT64_MAX - (*ptr - '0')) {
              aff_copy(stdscr);
              wmove(stdscr, LINES/2, 0);
              wprintw(stdscr, "Error: Width value too large");
              wrefresh(stdscr);
              wgetch(stdscr);
              return;
            }
            width += (*ptr - '0');
            ptr++;
          }

          if(*ptr == 'x') {
            ptr++;
            /* Parse height with overflow check */
            while(*ptr && isdigit(*ptr)) {
              if (height > UINT64_MAX / 10) {
                aff_copy(stdscr);
                wmove(stdscr, LINES/2, 0);
                wprintw(stdscr, "Error: Height value too large");
                wrefresh(stdscr);
                wgetch(stdscr);
                return;
              }
              height = height * 10;
              if (height > UINT64_MAX - (*ptr - '0')) {
                aff_copy(stdscr);
                wmove(stdscr, LINES/2, 0);
                wprintw(stdscr, "Error: Height value too large");
                wrefresh(stdscr);
                wgetch(stdscr);
                return;
              }
              height += (*ptr - '0');
              ptr++;
            }
          }
          /* Check for overflow and reasonable limits */
          if (width > UINT32_MAX || height > UINT32_MAX) {
            /* Show error message */
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Width and height must be <= %u", UINT32_MAX);
            wrefresh(stdscr);
            wgetch(stdscr);
            return; /* Don't update the filter */
          }

          if (width > 0 && height > 0 && height <= UINT64_MAX / width) {
            uint64_t calculated_pixels = (uint64_t)width * height;

            /* Check if min > max */
            if (filter->max_pixels > 0 && calculated_pixels > filter->max_pixels) {
              aff_copy(stdscr);
              wmove(stdscr, LINES/2, 0);
              wprintw(stdscr, "Error: Min pixels (%lu) cannot be greater than max pixels (%lu)",
                      (unsigned long)calculated_pixels, (unsigned long)filter->max_pixels);
              wrefresh(stdscr);
              wgetch(stdscr);
              return;
            }

            filter->min_pixels = calculated_pixels;
            /* Save the original format user entered */
            snprintf(pixels_min_format, sizeof(pixels_min_format), "%s", input);
          } else {
            /* Show overflow error */
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Width x Height calculation overflow");
            wrefresh(stdscr);
            wgetch(stdscr);
            return; /* Don't update the filter */
          }
        } else {
          /* Parse as plain number using strtoull for safety */
          char *endptr;
          errno = 0;
          uint64_t val = strtoull(input, &endptr, 10);

          /* Check for overflow or parsing errors */
          if (errno == ERANGE) {
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Value too large (max: %lu)", UINT64_MAX);
            wrefresh(stdscr);
            wgetch(stdscr);
            return;
          }

          /* Check if whole string was parsed */
          if (*endptr != '\0') {
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Invalid number format");
            wrefresh(stdscr);
            wgetch(stdscr);
            return;
          }

          /* Check if min > max */
          if (filter->max_pixels > 0 && val > filter->max_pixels) {
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Min pixels (%lu) cannot be greater than max pixels (%lu)",
                    (unsigned long)val, (unsigned long)filter->max_pixels);
            wrefresh(stdscr);
            wgetch(stdscr);
            return;
          }

          filter->min_pixels = val;
          /* Save the original format user entered */
          snprintf(pixels_min_format, sizeof(pixels_min_format), "%s", input);
        }
        /* Clear width/height min when setting pixels min */
        filter->min_width = 0;
        filter->min_height = 0;
        break;
      case 6: /* pixels max */
        /* Check string length first to prevent buffer overflows */
        if (strlen(input) > 31) {
          aff_copy(stdscr);
          wmove(stdscr, LINES/2, 0);
          wprintw(stdscr, "Error: Input too long");
          wrefresh(stdscr);
          wgetch(stdscr);
          return;
        }

        /* Check if it's WIDTHxHEIGHT format */
        if(strchr(input, 'x') != NULL) {
          uint64_t width = 0, height = 0;
          char *ptr = input;

          /* Parse width with overflow check */
          while(*ptr && isdigit(*ptr)) {
            if (width > UINT64_MAX / 10) {
              aff_copy(stdscr);
              wmove(stdscr, LINES/2, 0);
              wprintw(stdscr, "Error: Width value too large");
              wrefresh(stdscr);
              wgetch(stdscr);
              return;
            }
            width = width * 10;
            if (width > UINT64_MAX - (*ptr - '0')) {
              aff_copy(stdscr);
              wmove(stdscr, LINES/2, 0);
              wprintw(stdscr, "Error: Width value too large");
              wrefresh(stdscr);
              wgetch(stdscr);
              return;
            }
            width += (*ptr - '0');
            ptr++;
          }

          if(*ptr == 'x') {
            ptr++;
            /* Parse height with overflow check */
            while(*ptr && isdigit(*ptr)) {
              if (height > UINT64_MAX / 10) {
                aff_copy(stdscr);
                wmove(stdscr, LINES/2, 0);
                wprintw(stdscr, "Error: Height value too large");
                wrefresh(stdscr);
                wgetch(stdscr);
                return;
              }
              height = height * 10;
              if (height > UINT64_MAX - (*ptr - '0')) {
                aff_copy(stdscr);
                wmove(stdscr, LINES/2, 0);
                wprintw(stdscr, "Error: Height value too large");
                wrefresh(stdscr);
                wgetch(stdscr);
                return;
              }
              height += (*ptr - '0');
              ptr++;
            }
          }
          /* Check for overflow and reasonable limits */
          if (width > UINT32_MAX || height > UINT32_MAX) {
            /* Show error message */
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Width and height must be <= %u", UINT32_MAX);
            wrefresh(stdscr);
            wgetch(stdscr);
            return; /* Don't update the filter */
          }

          if (width > 0 && height > 0 && height <= UINT64_MAX / width) {
            uint64_t calculated_pixels = (uint64_t)width * height;

            /* Check if max < min */
            if (filter->min_pixels > 0 && calculated_pixels < filter->min_pixels) {
              aff_copy(stdscr);
              wmove(stdscr, LINES/2, 0);
              wprintw(stdscr, "Error: Max pixels (%lu) cannot be less than min pixels (%lu)",
                      (unsigned long)calculated_pixels, (unsigned long)filter->min_pixels);
              wrefresh(stdscr);
              wgetch(stdscr);
              return;
            }

            filter->max_pixels = calculated_pixels;
            /* Save the original format user entered */
            snprintf(pixels_max_format, sizeof(pixels_max_format), "%s", input);
          } else {
            /* Show overflow error */
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Width x Height calculation overflow");
            wrefresh(stdscr);
            wgetch(stdscr);
            return; /* Don't update the filter */
          }
        } else {
          /* Parse as plain number with overflow protection */
          uint64_t val = 0;
          char *ptr = input;

          /* Skip whitespace */
          while (*ptr == ' ' || *ptr == '\t') ptr++;

          /* Parse digits with overflow check */
          while (*ptr && isdigit(*ptr)) {
            /* Check for overflow before multiplying */
            if (val > UINT64_MAX / 10) {
              aff_copy(stdscr);
              wmove(stdscr, LINES/2, 0);
              wprintw(stdscr, "Error: Value too large (max: %lu)", UINT64_MAX);
              wrefresh(stdscr);
              wgetch(stdscr);
              return;
            }
            val = val * 10;

            /* Check for overflow before adding */
            if (val > UINT64_MAX - (*ptr - '0')) {
              aff_copy(stdscr);
              wmove(stdscr, LINES/2, 0);
              wprintw(stdscr, "Error: Value too large (max: %lu)", UINT64_MAX);
              wrefresh(stdscr);
              wgetch(stdscr);
              return;
            }
            val += (*ptr - '0');
            ptr++;
          }

          /* Check if max < min */
          if (filter->min_pixels > 0 && val < filter->min_pixels) {
            aff_copy(stdscr);
            wmove(stdscr, LINES/2, 0);
            wprintw(stdscr, "Error: Max pixels (%lu) cannot be less than min pixels (%lu)",
                    (unsigned long)val, (unsigned long)filter->min_pixels);
            wrefresh(stdscr);
            wgetch(stdscr);
            return;
          }

          filter->max_pixels = val;
          /* Save the original format user entered */
          snprintf(pixels_max_format, sizeof(pixels_max_format), "%s", input);
        }
        /* Clear width/height max when setting pixels max */
        filter->max_width = 0;
        filter->max_height = 0;
        break;
    }
  } else {
    /* Empty input - clear the field */
    switch(field_num) {
      case 1: filter->min_width = 0; break;
      case 2: filter->max_width = 0; break;
      case 3: filter->min_height = 0; break;
      case 4: filter->max_height = 0; break;
      case 5: filter->min_pixels = 0; pixels_min_format[0] = '\0'; break;
      case 6: filter->max_pixels = 0; pixels_max_format[0] = '\0'; break;
    }
  }

  /* Validate min <= max constraints */
  if (filter->min_width > 0 && filter->max_width > 0 && filter->min_width > filter->max_width) {
    filter->max_width = filter->min_width;
  }
  if (filter->min_height > 0 && filter->max_height > 0 && filter->min_height > filter->max_height) {
    filter->max_height = filter->min_height;
  }
  if (filter->min_pixels > 0 && filter->max_pixels > 0 && filter->min_pixels > filter->max_pixels) {
    filter->max_pixels = filter->min_pixels;
  }
}

static void interface_edit_filesize_field(file_size_filter_t *filter, int field_num)
{
  char input[32];
  char prompt[64];
  char current_value[32] = "";
  int ch;
  int input_pos = 0;
  int prompt_len = 44;

  /* Prepare current value and prompt */
  switch(field_num) {
    case 1: /* min file size */
      format_filesize_input(filter->min_file_size, current_value, sizeof(current_value));
      snprintf(prompt, sizeof(prompt), "Min file size (e.g. 100k, 2m): ");
      break;
    case 2: /* max file size */
      format_filesize_input(filter->max_file_size, current_value, sizeof(current_value));
      snprintf(prompt, sizeof(prompt), "Max file size (e.g. 2m, 1g): ");
      break;
    default:
      return;
  }

  /* Show input dialog */
  aff_copy(stdscr);
  wmove(stdscr, LINES/2-1, 0);
  wprintw(stdscr, "%s", prompt);
  wmove(stdscr, LINES/2, 0);
  wprintw(stdscr, "Current: %s", strlen(current_value) > 0 ? current_value : "none");
  wmove(stdscr, LINES/2+1, 0);
  wprintw(stdscr, "New value (empty to clear, Esc to cancel): ");
  wrefresh(stdscr);

  input[0] = '\0';
  wmove(stdscr, LINES/2+1, prompt_len);
  wrefresh(stdscr);

  echo();
  while (1) {
    ch = wgetch(stdscr);

    if (ch == key_ESC) {
      noecho();
      return;
    }
    else if (ch == '\n' || ch == '\r') {
      break;
    }
    else if (ch == KEY_BACKSPACE || ch == 127 || ch == 8) {
      if (input_pos > 0) {
        input_pos--;
        input[input_pos] = '\0';
        wmove(stdscr, LINES/2+1, prompt_len + input_pos);
        waddch(stdscr, ' ');
        wmove(stdscr, LINES/2+1, prompt_len + input_pos);
        wrefresh(stdscr);
      }
    }
    else if (ch >= 32 && ch <= 126 && input_pos < (int)sizeof(input)-2) {
      input[input_pos] = ch;
      input_pos++;
      input[input_pos] = '\0';
      wmove(stdscr, LINES/2+1, prompt_len + input_pos - 1);
      waddch(stdscr, ch);
      wrefresh(stdscr);
    }
  }
  noecho();

  /* Parse and apply input */
  if (strlen(input) > 0) {
    char *ptr = input;
    uint64_t val = parse_size_with_units(&ptr);

    switch(field_num) {
      case 1: /* min file size */
        filter->min_file_size = val;
        break;
      case 2: /* max file size */
        /* Validate max_file_size >= 1KB for optimal performance */
        if(val > 0 && val < 1024) {
          aff_copy(stdscr);
          wmove(stdscr, LINES/2, 0);
          wprintw(stdscr, "ERROR: Max file size must be at least 1KB\n");
          wprintw(stdscr, "Press any key to continue...");
          wrefresh(stdscr);
          wgetch(stdscr);
          return;
        }
        filter->max_file_size = val;
        break;
    }
  } else {
    /* Empty input - clear the field */
    switch(field_num) {
      case 1:
        filter->min_file_size = 0;
        break;
      case 2:
        filter->max_file_size = 0;
        break;
    }
  }

  /* Adjust max to equal min if min > max */
  if(filter->min_file_size > 0 && filter->max_file_size > 0 &&
     filter->min_file_size > filter->max_file_size) {
    filter->max_file_size = filter->min_file_size;
  }
}

static void interface_filesize_photorec_ncurses(struct ph_options *options)
{
  int field_selected = 1;  /* 1=min, 2=max */

  while (1)
  {
    int key;
    char min_str[32] = "";
    char max_str[32] = "";

    /* Format current values */
    format_filesize_input(options->file_size_filter.min_file_size, min_str, sizeof(min_str));
    format_filesize_input(options->file_size_filter.max_file_size, max_str, sizeof(max_str));

    /* Display interface */
    aff_copy(stdscr);
    wmove(stdscr, 4, 0);
    wprintw(stdscr, "File size filters\n");
    wmove(stdscr, 5, 0);
    wprintw(stdscr, "Note: These filters apply to all file types\n");

    /* Empty line */
    wmove(stdscr, 7, 0);
    wprintw(stdscr, "\n");

    /* Header row */
    wmove(stdscr, 8, 0);
    wprintw(stdscr, "                           min            max");

    /* File size row */
    wmove(stdscr, 9, 0);
    wprintw(stdscr, "File size:                 ");
    if (field_selected == 1) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[%-10s]", strlen(min_str) > 0 ? min_str : " disabled");
    if (field_selected == 1) wattroff(stdscr, A_REVERSE);
    wprintw(stdscr, " - ");
    if (field_selected == 2) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[%-10s]", strlen(max_str) > 0 ? max_str : " disabled");
    if (field_selected == 2) wattroff(stdscr, A_REVERSE);

    wmove(stdscr, 12, 0);
    wprintw(stdscr, "Use Arrow keys to select field, Enter to edit, 'c' to clear, 'q' to quit");

    wrefresh(stdscr);

    /* Handle input */
    key = wgetch(stdscr);
    switch(key)
    {
      case KEY_LEFT:
        if (field_selected == 2) field_selected = 1;
        break;
      case KEY_RIGHT:
        if (field_selected == 1) field_selected = 2;
        break;
      case '\n':
      case '\r':
      case KEY_ENTER:
        if (field_selected >= 1 && field_selected <= 2) {
          interface_edit_filesize_field(&options->file_size_filter, field_selected);
        }
        break;
      case 'c':
      case 'C':
        /* Clear all file size filters */
        options->file_size_filter.min_file_size = 0;
        options->file_size_filter.max_file_size = 0;
        field_selected = 1;
        break;
      case key_ESC:
      case 'q':
      case 'Q':
        return;
    }
  }
}

void interface_imagesize_photorec_ncurses(struct ph_options *options)
{
  int field_selected = 1;  /* 1=width_min, 2=width_max, 3=height_min, 4=height_max, 5=pixels_min, 6=pixels_max */

  while (1)
  {
    int key;
    char width_min_str[16] = "";
    char width_max_str[16] = "";
    char height_min_str[16] = "";
    char height_max_str[16] = "";
    char pixels_min_str[32] = "";
    char pixels_max_str[32] = "";

    /* Check which fields should be disabled based on specific values set */
    int pixels_min_active = (options->image_filter.min_pixels > 0);
    int pixels_max_active = (options->image_filter.max_pixels > 0);
    int dimensions_min_active = (options->image_filter.min_width > 0 || options->image_filter.min_height > 0);
    int dimensions_max_active = (options->image_filter.max_width > 0 || options->image_filter.max_height > 0);

    /* Width strings */
    if (options->image_filter.min_width > 0) {
      snprintf(width_min_str, sizeof(width_min_str), "%u", options->image_filter.min_width);
    }
    if (options->image_filter.max_width > 0) {
      snprintf(width_max_str, sizeof(width_max_str), "%u", options->image_filter.max_width);
    }

    /* Height strings */
    if (options->image_filter.min_height > 0) {
      snprintf(height_min_str, sizeof(height_min_str), "%u", options->image_filter.min_height);
    }
    if (options->image_filter.max_height > 0) {
      snprintf(height_max_str, sizeof(height_max_str), "%u", options->image_filter.max_height);
    }

    /* Pixels strings - show exactly what user entered */
    if (options->image_filter.min_pixels > 0) {
      if (strlen(pixels_min_format) > 0) {
        snprintf(pixels_min_str, sizeof(pixels_min_str), "%s", pixels_min_format);
      } else {
        /* Fallback - show as plain number */
        snprintf(pixels_min_str, sizeof(pixels_min_str), "%lu", (unsigned long)options->image_filter.min_pixels);
      }
    }
    if (options->image_filter.max_pixels > 0) {
      if (strlen(pixels_max_format) > 0) {
        snprintf(pixels_max_str, sizeof(pixels_max_str), "%s", pixels_max_format);
      } else {
        /* Fallback - show as plain number */
        snprintf(pixels_max_str, sizeof(pixels_max_str), "%lu", (unsigned long)options->image_filter.max_pixels);
      }
    }

    /* Display interface */
    aff_copy(stdscr);
    wmove(stdscr, 4, 0);
    wprintw(stdscr, "Image size filters : %s\n", has_any_image_size_filter(&options->image_filter) ? "Enabled" : "Disabled");
    wmove(stdscr, 5, 0);
    wprintw(stdscr, "Note: These filters apply only to JPG and PNG files\n");

    /* Empty line */
    wmove(stdscr, 7, 0);
    wprintw(stdscr, "\n");

    /* Header row */
    wmove(stdscr, 8, 0);
    wprintw(stdscr, "                           min            max");

    /* Width row */
    wmove(stdscr, 9, 0);
    wprintw(stdscr, "Width (pixels):            ");
    if (pixels_min_active) wattron(stdscr, A_DIM);
    if (field_selected == 1) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[%-10s]", strlen(width_min_str) > 0 ? width_min_str : " disabled");
    if (field_selected == 1) wattroff(stdscr, A_REVERSE);
    if (pixels_min_active) wattroff(stdscr, A_DIM);
    wprintw(stdscr, " - ");
    if (pixels_max_active) wattron(stdscr, A_DIM);
    if (field_selected == 2) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[%-10s]", strlen(width_max_str) > 0 ? width_max_str : " disabled");
    if (field_selected == 2) wattroff(stdscr, A_REVERSE);
    if (pixels_max_active) wattroff(stdscr, A_DIM);

    /* Height row */
    wmove(stdscr, 10, 0);
    wprintw(stdscr, "Height (pixels):           ");
    if (pixels_min_active) wattron(stdscr, A_DIM);
    if (field_selected == 3) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[%-10s]", strlen(height_min_str) > 0 ? height_min_str : " disabled");
    if (field_selected == 3) wattroff(stdscr, A_REVERSE);
    if (pixels_min_active) wattroff(stdscr, A_DIM);
    wprintw(stdscr, " - ");
    if (pixels_max_active) wattron(stdscr, A_DIM);
    if (field_selected == 4) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[%-10s]", strlen(height_max_str) > 0 ? height_max_str : " disabled");
    if (field_selected == 4) wattroff(stdscr, A_REVERSE);
    if (pixels_max_active) wattroff(stdscr, A_DIM);

    /* Resolution row */
    wmove(stdscr, 11, 0);
    wprintw(stdscr, "Resolution (WIDTHxHEIGHT): ");
    if (dimensions_min_active) wattron(stdscr, A_DIM);
    if (field_selected == 5) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[%-10s]", strlen(pixels_min_str) > 0 ? pixels_min_str : " disabled");
    if (field_selected == 5) wattroff(stdscr, A_REVERSE);
    if (dimensions_min_active) wattroff(stdscr, A_DIM);
    wprintw(stdscr, " - ");
    if (dimensions_max_active) wattron(stdscr, A_DIM);
    if (field_selected == 6) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[%-10s]", strlen(pixels_max_str) > 0 ? pixels_max_str : " disabled");
    if (field_selected == 6) wattroff(stdscr, A_REVERSE);
    if (dimensions_max_active) wattroff(stdscr, A_DIM);

    /* Presets section */
    wmove(stdscr, 13, 0);
    wprintw(stdscr, "\nQuick presets (min resolution):");
    wmove(stdscr, 15, 0);
    if (field_selected == 7) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[1] VGA (640x480)");
    if (field_selected == 7) wattroff(stdscr, A_REVERSE);
    wprintw(stdscr, "  ");
    if (field_selected == 8) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[2] HD (1280x720)");
    if (field_selected == 8) wattroff(stdscr, A_REVERSE);
    wprintw(stdscr, "  ");
    if (field_selected == 9) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[3] FullHD (1920x1080)");
    if (field_selected == 9) wattroff(stdscr, A_REVERSE);
    wmove(stdscr, 16, 0);
    if (field_selected == 10) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[4] 2K (2560x1440)");
    if (field_selected == 10) wattroff(stdscr, A_REVERSE);
    wprintw(stdscr, "  ");
    if (field_selected == 11) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[5] 4K (3840x2160)");
    if (field_selected == 11) wattroff(stdscr, A_REVERSE);
    wprintw(stdscr, "  ");
    if (field_selected == 12) wattron(stdscr, A_REVERSE);
    wprintw(stdscr, "[6] 8K (7680x4320)");
    if (field_selected == 12) wattroff(stdscr, A_REVERSE);

    wmove(stdscr, 18, 0);
    wprintw(stdscr, "Use Arrow keys, Enter to edit/apply preset, 'c' to clear, 'q' to quit");

    wrefresh(stdscr);

    /* Handle input */
    key = wgetch(stdscr);
    switch(key)
    {
      case KEY_UP:
        if (field_selected > 9) field_selected -= 3; /* Presets row */
        else if (field_selected >= 7 && field_selected <= 9) field_selected = 1; /* From presets to fields */
        else if (field_selected > 2) field_selected -= 2;
        break;
      case KEY_DOWN:
        if (field_selected <= 4) field_selected += 2;
        else if (field_selected <= 6) field_selected = 7; /* To presets */
        else if (field_selected <= 8) field_selected += 3;
        break;
      case KEY_LEFT:
        if (field_selected >= 7 && field_selected <= 12) {
          /* Navigate presets */
          if (field_selected > 7) field_selected -= 1;
        } else if (field_selected % 2 == 0 && field_selected > 1) {
          field_selected -= 1;
        }
        break;
      case KEY_RIGHT:
        if (field_selected >= 7 && field_selected <= 12) {
          /* Navigate presets */
          if (field_selected < 12) field_selected += 1;
        } else if (field_selected % 2 == 1 && field_selected < 6) {
          field_selected += 1;
        }
        break;
      case '1':
      case '2':
      case '3':
      case '4':
      case '5':
      case '6':
        /* Quick preset selection by number key */
        field_selected = 6 + (key - '0');
        /* Fall through to apply preset */
      case '\n':
      case '\r':
      case KEY_ENTER:
        if (field_selected >= 1 && field_selected <= 6) {
          /* Check if field is disabled before allowing edit */
          int can_edit = 1;
          if ((field_selected == 1 || field_selected == 3) && pixels_min_active) can_edit = 0;
          if ((field_selected == 2 || field_selected == 4) && pixels_max_active) can_edit = 0;
          if (field_selected == 5 && dimensions_min_active) can_edit = 0;
          if (field_selected == 6 && dimensions_max_active) can_edit = 0;

          if (can_edit) {
            interface_edit_image_filter_field(&options->image_filter, field_selected);
          }
        } else if (field_selected >= 7 && field_selected <= 12) {
          /* Apply preset */
          options->image_filter.min_pixels = 0;
          options->image_filter.max_pixels = 0;
          pixels_min_format[0] = '\0';
          pixels_max_format[0] = '\0';

          switch(field_selected) {
            case 7: /* VGA 640x480 */
              options->image_filter.min_width = 640;
              options->image_filter.min_height = 480;
              break;
            case 8: /* HD 1280x720 */
              options->image_filter.min_width = 1280;
              options->image_filter.min_height = 720;
              break;
            case 9: /* FullHD 1920x1080 */
              options->image_filter.min_width = 1920;
              options->image_filter.min_height = 1080;
              break;
            case 10: /* 2K 2560x1440 */
              options->image_filter.min_width = 2560;
              options->image_filter.min_height = 1440;
              break;
            case 11: /* 4K 3840x2160 */
              options->image_filter.min_width = 3840;
              options->image_filter.min_height = 2160;
              break;
            case 12: /* 8K 7680x4320 */
              options->image_filter.min_width = 7680;
              options->image_filter.min_height = 4320;
              break;
          }
        }
        break;
      case 'c':
      case 'C':
        /* Clear all image dimension filters (keep file size intact) */
        options->image_filter.min_pixels = 0;
        options->image_filter.max_pixels = 0;
        options->image_filter.min_width = 0;
        options->image_filter.max_width = 0;
        options->image_filter.min_height = 0;
        options->image_filter.max_height = 0;
        pixels_min_format[0] = '\0';
        pixels_max_format[0] = '\0';
        field_selected = 1;
        break;
      case key_ESC:
      case 'q':
      case 'Q':
        return;
    }
  }
}

#endif
