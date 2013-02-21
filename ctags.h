/*
*   $Id: ctags.h 702 2009-03-14 03:52:21Z dhiebert $
*
*   Copyright (c) 1996-2002, Darren Hiebert
*
*   This source code is released for free distribution under the terms of the
*   GNU General Public License.
*
*   Program definitions
*/
#ifndef _CTAGS_H
#define _CTAGS_H

/*
*   MACROS
*/
#ifndef PROGRAM_VERSION
# define PROGRAM_VERSION "5.8"
#endif
#define PROGRAM_NAME      "Exuberant Ctags"
#define PROGRAM_URL       "http://ctags.sourceforge.net"
#define PROGRAM_COPYRIGHT "Copyright (C) 1996-2009"
#define AUTHOR_NAME       "Darren Hiebert"
#define AUTHOR_EMAIL      "dhiebert@users.sourceforge.net"

#ifdef KANJI
# define PROGRAM_JP_VERSION	"J2"
# define JP_AUTHOR_NAME		"HIGASHI Hirohito"
# define JP_AUTHOR_URL		"http://hp.vector.co.jp/authors/VA025040/"
# define JP_AUTHOR_TWITTER	"Twitter: @h_east"
#endif

#endif	/* _CTAGS_H */

/* vi:set tabstop=4 shiftwidth=4: */
