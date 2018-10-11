/*
 * Copyright (C) Lucent Technologies 1997
 * All Rights Reserved
 *
 * Permission to use, copy, modify, and distribute this software and
 * its documentation for any purpose and without fee is hereby
 * granted, provided that the above copyright notice appear in all
 * copies and that both that the copyright notice and this
 * permission notice and warranty disclaimer appear in supporting
 * documentation, and that the name Lucent Technologies or any of
 * its entities not be used in advertising or publicity pertaining
 * to distribution of the software without specific, written prior
 * permission.
 *
 * LUCENT DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE,
 * INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS.
 * IN NO EVENT SHALL LUCENT OR ANY OF ITS ENTITIES BE LIABLE FOR ANY
 * SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER
 * IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION,
 * ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF
 * THIS SOFTWARE.
 */

/*
 * CDDL HEADER START
 *
 * The contents of this file are subject to the terms of the
 * Common Development and Distribution License (the "License").
 * You may not use this file except in compliance with the License.
 *
 * You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
 * or http://www.opensolaris.org/os/licensing.
 * See the License for the specific language governing permissions
 * and limitations under the License.
 *
 * When distributing Covered Code, include this CDDL HEADER in each
 * file and include the License file at usr/src/OPENSOLARIS.LICENSE.
 * If applicable, add the following below this CDDL HEADER, with the
 * fields enclosed by brackets "[]" replaced with your own identifying
 * information: Portions Copyright [yyyy] [name of copyright owner]
 *
 * CDDL HEADER END
 */

/*
 * Copyright 2006 Sun Microsystems, Inc.  All rights reserved.
 * Use is subject to license terms.
 */

/*	Copyright (c) 1984, 1986, 1987, 1988, 1989 AT&T	*/
/*	  All Rights Reserved  	*/

/*	Copyright (c) Lucent Technologies 1997	*/
/*	  All Rights Reserved  	*/

#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <stdlib.h>
#include <stdarg.h>
#include "awk.h"
#include "y.tab.h"

static FILE	*infile	= NULL;
static char	*file	= "";
char	*record;
size_t	recsize;
static char	*fields;
static size_t	fieldssize = LINE_INCR;

char	inputFS[100] = " ";

int	donefld;	/* 1 = implies rec broken into fields */
int	donerec;	/* 1 = record is valid (no flds have changed) */

static struct fldtab_chunk {
	struct fldtab_chunk	*next;
	Cell			fields[FLD_INCR];
} *fldtab_head, *fldtab_tail;

static	size_t	fldtab_maxidx;


static int	maxfld	= 0;	/* last used field */
static int	argno	= 1;	/* current input argument number */

static	char	*getargv(int);
static	void	cleanfld(int, int);
static	int	refldbld(const char *, const char *);
static	void	bcheck2(int, int, int);
static	void	eprint(void);
static	void	bclass(int);

static void
initgetrec(void)
{
	int i;
	char *p;

	for (i = 1; i < *ARGC; i++) {
		p = getargv(i); /* find 1st real filename */
		if (p == NULL || *p == '\0') {  /* deleted or zapped */
			argno++;
			continue;
		}
		if (!isclvar(p)) {
			(void) setsval(lookup("FILENAME", symtab), p);
			return;
		}
		setclvar(p);	/* a commandline assignment before filename */
		argno++;
	}
	infile = stdin;		/* no filenames, so use stdin */
}

static int firsttime = 1;

/*
 * get next input record
 * note: cares whether buf == record
 */
int
getrec(char **pbuf, size_t *pbufsize)
{
	int c;
	char	*buf = *pbuf, *nbuf;
	uschar saveb0;
	size_t	len, savebufsize = *pbufsize;

	if (firsttime) {
		firsttime = 0;
		initgetrec();
	}
	dprintf(("RS=<%s>, FS=<%s>, ARGC=%f, FILENAME=%s\n",
	    *RS, *FS, *ARGC, *FILENAME));
	if (pbuf == &record) {
		donefld = 0;
		donerec = 1;
	}
	saveb0 = buf[0];
	while (argno < *ARGC || infile == stdin) {
		dprintf(("argno=%d, file=|%s|\n", argno, file));
		if (infile == NULL) {	/* have to open a new file */
			file = getargv(argno);
			if (file == NULL || *file == '\0') {
				/* deleted or zapped */
				argno++;
				continue;
			}
			if (isclvar(file)) {
				/* a var=value arg */
				setclvar(file);
				argno++;
				continue;
			}
			*FILENAME = file;
			dprintf(("opening file %s\n", file));
			if (*file == '-' && *(file+1) == '\0')
				infile = stdin;
			else if ((infile = fopen(file, "rF")) == NULL)
				FATAL("can't open file %s", file);
			(void) setfval(fnrloc, 0.0);
		}
		c = readrec(&nbuf, &len, infile);
		expand_buf(pbuf, pbufsize, len);
		buf = *pbuf;
		(void) memcpy(buf, nbuf, len);
		buf[len] = '\0';
		free(nbuf);

		if (c != 0 || buf[0] != '\0') {	/* normal record */
			if (pbuf == &record) {
				if (freeable(recloc))
					xfree(recloc->sval);
				recloc->sval = record;
				recloc->tval = REC | STR | DONTFREE;
				if (is_number(recloc->sval)) {
					recloc->fval =
					    atof(recloc->sval);
					recloc->tval |= NUM;
				}
			}
			(void) setfval(nrloc, nrloc->fval+1);
			(void) setfval(fnrloc, fnrloc->fval+1);
			return (1);
		}
		/* EOF arrived on this file; set up next */
		if (infile != stdin)
			(void) fclose(infile);
		infile = NULL;
		argno++;
	}
	buf[0] = saveb0;
	*pbuf = buf;
	*pbufsize = savebufsize;
	return (0);	/* true end of file */
}

void
nextfile(void)
{
	if (infile != NULL && infile != stdin)
		(void) fclose(infile);
	infile = NULL;
	argno++;
}

int
readrec(char **bufp, size_t *sizep, FILE *inf)	/* read one record into buf */
{
	int sep, c;
	char	*buf;
	int	count;
	size_t	bufsize;

	init_buf(&buf, &bufsize, LINE_INCR);

	if (strlen(*FS) >= sizeof (inputFS))
		FATAL("field separator %.10s... is too long", *FS);
	(void) strcpy(inputFS, *FS);	/* for subsequent field splitting */
	if ((sep = **RS) == 0) {
		sep = '\n';
		/* skip leading \n's */
		while ((c = getc(inf)) == '\n' && c != EOF)
			;
		if (c != EOF)
			(void) ungetc(c, inf);
	}
	count = 0;
	for (;;) {
		while ((c = getc(inf)) != sep && c != EOF) {
			expand_buf(&buf, &bufsize, count);
			buf[count++] = c;
		}
		if (**RS == sep || c == EOF)
			break;
		if ((c = getc(inf)) == '\n' || c == EOF) /* 2 in a row */
			break;
		expand_buf(&buf, &bufsize, count + 1);
		buf[count++] = '\n';
		buf[count++] = c;
	}
	buf[count] = '\0';
	dprintf(("readrec saw <%s>, returns %d\n",
	    buf, c == EOF && count == 0 ? 0 : 1));
	*bufp = buf;
	*sizep = count;
	return (c == EOF && count == 0 ? 0 : 1);
}

/* get ARGV[n] */
static char *
getargv(int n)
{
	Cell *x;
	char *s, temp[50];
	extern Array *ARGVtab;

	(void) sprintf(temp, "%d", n);
	if (lookup(temp, ARGVtab) == NULL)
		return (NULL);
	x = setsymtab(temp, "", 0.0, STR, ARGVtab);
	s = getsval(x);
	dprintf(("getargv(%d) returns |%s|\n", n, s));
	return (s);
}

void
setclvar(char *s)	/* set var=value from s */
{
	char *p;
	Cell *q;

	for (p = s; *p != '='; p++)
		;
	*p++ = 0;
	p = qstring(p, '\0');
	q = setsymtab(s, p, 0.0, STR, symtab);
	(void) setsval(q, p);
	if (is_number(q->sval)) {
		q->fval = atof(q->sval);
		q->tval |= NUM;
	}
	dprintf(("command line set %s to |%s|\n", s, p));
	free(p);
}

void
fldbld(void)	/* create fields from current record */
{
	char *r, *fr, sep;
	Cell *p;
	int i;
	size_t	len;

	if (donefld)
		return;
	if (!isstr(recloc))
		(void) getsval(recloc);
	r = recloc->sval;	/* was record! */

	/* make sure fields is always allocated */
	adjust_buf(&fields, fieldssize);

	/*
	 * make sure fields has enough size. We don't expand the buffer
	 * in the middle of the loop, since p->sval has already pointed
	 * the address in the fields.
	 */
	len = strlen(r) + 1;
	expand_buf(&fields, &fieldssize, len);
	fr = fields;

	i = 0;	/* number of fields accumulated here */
	(void) strcpy(inputFS, *FS);
	if (strlen(inputFS) > 1) {	/* it's a regular expression */
		i = refldbld(r, inputFS);
	} else if ((sep = *inputFS) == ' ') {	/* default whitespace */
		for (i = 0; ; ) {
			while (*r == ' ' || *r == '\t' || *r == '\n')
				r++;
			if (*r == '\0')
				break;
			i++;
			p = getfld(i);
			if (freeable(p))
				xfree(p->sval);
			p->sval = fr;
			p->tval = FLD | STR | DONTFREE;
			do
				*fr++ = *r++;
			while (*r != ' ' && *r != '\t' && *r != '\n' &&
			    *r != '\0')
				;
			*fr++ = 0;
		}
		*fr = 0;
	} else if ((sep = *inputFS) == 0) {
		/* new: FS="" => 1 char/field */
		for (i = 0; *r != '\0'; r++) {
			char buf[2];
			i++;
			p = getfld(i);
			if (freeable(p))
				xfree(p->sval);
			buf[0] = *r;
			buf[1] = '\0';
			p->sval = tostring(buf);
			p->tval = FLD | STR;
		}
		*fr = '\0';
	} else if (*r != '\0') {	/* if 0, it's a null field */
		/*
		 * subtlecase : if length(FS) == 1 && length(RS > 0)
		 * \n is NOT a field separator (cf awk book 61,84).
		 * this variable is tested in the inner while loop.
		 */
		int rtest = '\n';  /* normal case */
		if (strlen(*RS) > 0)
			rtest = '\0';
		for (;;) {
			i++;
			p = getfld(i);
			if (freeable(p))
				xfree(p->sval);
			p->sval = fr;
			p->tval = FLD | STR | DONTFREE;
			/* \n is always a separator */
			while (*r != sep && *r != rtest && *r != '\0')
				*fr++ = *r++;
			*fr++ = '\0';
			if (*r++ == '\0')
				break;
		}
		*fr = '\0';
	}
	/* clean out junk from previous record */
	cleanfld(i, maxfld);
	maxfld = i;
	donefld = 1;
	for (i = 1; i <= maxfld; i++) {
		p = getfld(i);
		if (is_number(p->sval)) {
			p->fval = atof(p->sval);
			p->tval |= NUM;
		}
	}

	(void) setfval(nfloc, (Awkfloat) maxfld);
	if (dbg) {
		for (i = 0; i <= maxfld; i++) {
			p = getfld(i);
			(void) printf("field %d: |%s|\n", i, p->sval);
		}
	}
}

static void
cleanfld(int n1, int n2)	/* clean out fields n1..n2 inclusive */
{
	Cell *p;
	int i;

	for (i = n2; i > n1; i--) {
		p = getfld(i);
		if (freeable(p))
			xfree(p->sval);
		p->sval = "";
		p->tval = FLD | STR | DONTFREE;
	}
}

void
newfld(int n)	/* add field n (after end) */
{
	if (n < 0)
		FATAL("accessing invalid field", record);
	(void) getfld(n);
	cleanfld(maxfld, n);
	maxfld = n;
	(void) setfval(nfloc, (Awkfloat)n);
}

/*
 * allocate field table. We don't reallocate the table since there
 * might be somewhere recording the address of the table.
 */
static void
morefld(void)
{
	int	i;
	struct fldtab_chunk *fldcp;
	Cell	*newfld;

	if ((fldcp = calloc(sizeof (struct fldtab_chunk), 1)) == NULL)
		FATAL("out of space in morefld");

	newfld = &fldcp->fields[0];
	for (i = 0; i < FLD_INCR; i++) {
		newfld[i].ctype = OCELL;
		newfld[i].csub = CFLD;
		newfld[i].nval = NULL;
		newfld[i].sval = "";
		newfld[i].fval = 0.0;
		newfld[i].tval = FLD|STR|DONTFREE;
		newfld[i].cnext = NULL;
	}
	/*
	 * link this field chunk
	 */
	if (fldtab_head == NULL)
		fldtab_head = fldcp;
	else
		fldtab_tail->next = fldcp;
	fldtab_tail = fldcp;
	fldcp->next = NULL;

	fldtab_maxidx += FLD_INCR;
}

Cell *
getfld(int idx)
{
	struct fldtab_chunk *fldcp;
	int	cbase;

	if (idx < 0)
		FATAL("trying to access field %d", idx);
	while (idx >= fldtab_maxidx)
		morefld();
	cbase = 0;
	for (fldcp = fldtab_head; fldcp != NULL; fldcp = fldcp->next) {
		if (idx < (cbase + FLD_INCR))
			return (&fldcp->fields[idx - cbase]);
		cbase += FLD_INCR;
	}
	/* should never happen */
	FATAL("trying to access invalid field %d", idx);
}

int
fldidx(Cell *vp)
{
	struct fldtab_chunk *fldcp;
	Cell	*tbl;
	int	cbase;

	cbase = 0;
	for (fldcp = fldtab_head; fldcp != NULL; fldcp = fldcp->next) {
		tbl = &fldcp->fields[0];
		if (vp >= tbl && vp < (tbl + FLD_INCR))
			return (cbase + (vp - tbl));
		cbase += FLD_INCR;
	}
	/* should never happen */
	FATAL("trying to access unknown field");
}

/* build fields from reg expr in FS */
static int
refldbld(const char *rec, const char *fs)
{
	char *fr;
	int i, tempstat;
	fa *pfa;
	Cell	*p;
	size_t	len;

	/* make sure fields is allocated */
	adjust_buf(&fields, fieldssize);
	fr = fields;
	*fr = '\0';
	if (*rec == '\0')
		return (0);

	len = strlen(rec) + 1;
	expand_buf(&fields, &fieldssize, len);
	fr = fields;

	pfa = makedfa(fs, 1);
	dprintf(("into refldbld, rec = <%s>, pat = <%s>\n", rec, fs));
	tempstat = pfa->initstat;
	for (i = 1; ; i++) {
		p = getfld(i);
		if (freeable(p))
			xfree(p->sval);
		p->tval = FLD | STR | DONTFREE;
		p->sval = fr;
		dprintf(("refldbld: i=%d\n", i));
		if (nematch(pfa, rec)) {
			pfa->initstat = 2;	/* horrible coupling to b.c */
			dprintf(("match %s (%d chars)\n", patbeg, patlen));
			(void) strncpy(fr, rec, patbeg-rec);
			fr += patbeg - rec + 1;
			*(fr-1) = '\0';
			rec = patbeg + patlen;
		} else {
			dprintf(("no match %s\n", rec));
			(void) strcpy(fr, rec);
			pfa->initstat = tempstat;
			break;
		}
	}
	return (i);
}

void
recbld(void)	/* create $0 from $1..$NF if necessary */
{
	int i;
	char *p;
	size_t cnt, len, olen;

	if (donerec == 1)
		return;
	cnt = 0;
	olen = strlen(*OFS);
	for (i = 1; i <= *NF; i++) {
		p = getsval(getfld(i));
		len = strlen(p);
		expand_buf(&record, &recsize, cnt + len + olen);
		(void) memcpy(&record[cnt], p, len);
		cnt += len;
		if (i < *NF) {
			(void) memcpy(&record[cnt], *OFS, olen);
			cnt += olen;
		}
	}
	record[cnt] = '\0';
	dprintf(("in recbld inputFS=%s, recloc=%p\n", inputFS, (void *)recloc));
	if (freeable(recloc))
		xfree(recloc->sval);
	recloc->tval = REC | STR | DONTFREE;
	recloc->sval = record;
	dprintf(("in recbld inputFS=%s, recloc=%p\n", inputFS, (void *)recloc));
	dprintf(("recbld = |%s|\n", record));
	donerec = 1;
}

Cell *
fieldadr(int n)
{
	if (n < 0)
		FATAL("trying to access field %d", n);
	return (getfld(n));
}

int	errorflag	= 0;

void
yyerror(const char *s)
{
	SYNTAX("%s", s);
}

void
SYNTAX(const char *fmt, ...)
{
	extern char *cmdname, *curfname;
	static int been_here = 0;
	va_list varg;

	if (been_here++ > 2)
		return;
	(void) fprintf(stderr, "%s: ", cmdname);
	va_start(varg, fmt);
	(void) vfprintf(stderr, fmt, varg);
	va_end(varg);
	(void) fprintf(stderr, " at source line %lld", lineno);
	if (curfname != NULL)
		(void) fprintf(stderr, " in function %s", curfname);
	if (compile_time == 1 && cursource() != NULL)
		(void) fprintf(stderr, " source file %s", cursource());
	(void) fprintf(stderr, "\n");
	errorflag = 2;
	eprint();
}

void
fpecatch(int n)
{
	FATAL("floating point exception %d", n);
}

extern int bracecnt, brackcnt, parencnt;

void
bracecheck(void)
{
	int c;
	static int beenhere = 0;

	if (beenhere++)
		return;
	while ((c = input()) != EOF && c != '\0')
		bclass(c);
	bcheck2(bracecnt, '{', '}');
	bcheck2(brackcnt, '[', ']');
	bcheck2(parencnt, '(', ')');
}

/*ARGSUSED*/
static void
bcheck2(int n, int c1, int c2)
{
	if (n == 1)
		(void) fprintf(stderr, gettext("\tmissing %c\n"), c2);
	else if (n > 1)
		(void) fprintf(stderr, gettext("\t%d missing %c's\n"), n, c2);
	else if (n == -1)
		(void) fprintf(stderr, gettext("\textra %c\n"), c2);
	else if (n < -1)
		(void) fprintf(stderr, gettext("\t%d extra %c's\n"), -n, c2);
}

void
FATAL(const char *fmt, ...)
{
	extern char *cmdname;
	va_list varg;

	(void) fflush(stdout);
	(void) fprintf(stderr, "%s: ", cmdname);
	va_start(varg, fmt);
	(void) vfprintf(stderr, fmt, varg);
	va_end(varg);
	error();
	if (dbg > 1)		/* core dump if serious debugging on */
		abort();
	exit(2);
}

void
WARNING(const char *fmt, ...)
{
	extern char *cmdname;
	va_list varg;

	(void) fflush(stdout);
	(void) fprintf(stderr, "%s: ", cmdname);
	va_start(varg, fmt);
	(void) vfprintf(stderr, fmt, varg);
	va_end(varg);
	error();
}

void
error(void)
{
	extern Node *curnode;

	(void) fprintf(stderr, "\n");
	if (compile_time != 2 && NR && *NR > 0) {
		(void) fprintf(stderr,
		    gettext(" input record number %g"), *FNR);
		if (strcmp(*FILENAME, "-") != 0)
			(void) fprintf(stderr, gettext(", file %s"), *FILENAME);
		(void) fprintf(stderr, "\n");
	}
	if (compile_time != 2 && curnode)
		(void) fprintf(stderr, gettext(" source line number %lld"),
		    curnode->lineno);
	else if (compile_time != 2 && lineno) {
		(void) fprintf(stderr,
		    gettext(" source line number %lld"), lineno);
	}
	if (compile_time == 1 && cursource() != NULL)
		(void) fprintf(stderr, gettext(" source file %s"), cursource());
	(void) fprintf(stderr, "\n");
	eprint();
}

static void
eprint(void)	/* try to print context around error */
{
	char *p, *q;
	int c;
	static int been_here = 0;
	extern char ebuf[], *ep;

	if (compile_time == 2 || compile_time == 0 || been_here++ > 0)
		return;
	if (ebuf == ep)
		return;
	p = ep - 1;
	if (p > ebuf && *p == '\n')
		p--;
	for (; p > ebuf && *p != '\n' && *p != '\0'; p--)
		;
	while (*p == '\n')
		p++;
	(void) fprintf(stderr, gettext(" context is\n\t"));
	for (q = ep-1; q >= p && *q != ' ' && *q != '\t' && *q != '\n'; q--)
		;
	for (; p < q; p++)
		if (*p)
			(void) putc(*p, stderr);
	(void) fprintf(stderr, " >>> ");
	for (; p < ep; p++)
		if (*p)
			(void) putc(*p, stderr);
	(void) fprintf(stderr, " <<< ");
	if (*ep)
		while ((c = input()) != '\n' && c != '\0' && c != EOF) {
			(void) putc(c, stderr);
			bclass(c);
		}
	(void) putc('\n', stderr);
	ep = ebuf;
}

static void
bclass(int c)
{
	switch (c) {
	case '{': bracecnt++; break;
	case '}': bracecnt--; break;
	case '[': brackcnt++; break;
	case ']': brackcnt--; break;
	case '(': parencnt++; break;
	case ')': parencnt--; break;
	}
}

double
errcheck(double x, const char *s)
{
	if (errno == EDOM) {
		errno = 0;
		WARNING("%s argument out of domain", s);
		x = 1;
	} else if (errno == ERANGE) {
		errno = 0;
		WARNING("%s result out of range", s);
		x = 1;
	}
	return (x);
}

int
isclvar(const char *s)	/* is s of form var=something ? */
{
	if (s != NULL) {

		/* Must begin with an underscore or alphabetic character */
		if (isalpha(*s) || (*s == '_')) {

			for (s++; *s; s++) {
				/*
				 * followed by a sequence of underscores,
				 * digits, and alphabetics
				 */
				if (!(isalnum(*s) || *s == '_')) {
					break;
				}
			}
			return (*s == '=' && *(s + 1) != '=');
		}
	}

	return (0);
}

#include <math.h>
int
is_number(const char *s)
{
	double r;
	char *ep;
	errno = 0;
	r = strtod(s, &ep);
	if (ep == s || r == HUGE_VAL || errno == ERANGE)
		return (0);
	while (*ep == ' ' || *ep == '\t' || *ep == '\n')
		ep++;
	if (*ep == '\0')
		return (1);
	else
		return (0);
}

void
init_buf(char **optr, size_t *sizep, size_t amt)
{
	char	*nptr = NULL;

	if ((nptr = malloc(amt)) == NULL)
		FATAL("out of space in init_buf");
	/* initial buffer should have NULL terminated */
	*nptr = '\0';
	if (sizep != NULL)
		*sizep = amt;
	*optr = nptr;
}

void
r_expand_buf(char **optr, size_t *sizep, size_t req)
{
	char	*nptr;
	size_t	amt, size = *sizep;

	if (size != 0 && req < (size - 1))
		return;
	amt = req + 1 - size;
	amt = (amt / LINE_INCR + 1) * LINE_INCR;

	if ((nptr = realloc(*optr, size + amt)) == NULL)
		FATAL("out of space in expand_buf");
	/* initial buffer should have NULL terminated */
	if (size == 0)
		*nptr = '\0';
	*sizep += amt;
	*optr = nptr;
}

void
adjust_buf(char **optr, size_t size)
{
	char	*nptr;

	if ((nptr = realloc(*optr, size)) == NULL)
		FATAL("out of space in adjust_buf");
	*optr = nptr;
}
