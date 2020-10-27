#
#  Makefile for dwarfdump
#  This is made very simple so it should work with
#  any 'make'.
#  The Makefile does assume that libdwarf is at ../libdwarf
#  from the dwarfdump2 source directory.
#

srcdir =	.


prefix =	/usr/local
exec_prefix =	${prefix}
bindir =	$(exec_prefix)/bin
libdir =	$(exec_prefix)/lib
mandir =        $(exec_prefix)/share/man
man1dir =       $(mandir)/man1


INSTALL =	/usr/bin/install -c
INSTALL_PROGRAM = ${INSTALL}
INSTALL_DATA =	${INSTALL} -m 644
DATAROOT =      ${prefix}/share
SHELL =		/bin/sh
CC =		gcc
AR =		ar
ARFLAGS =	@ARFLAGS@
RM =		rm
RANLIB =	ranlib
DEFS =		-DHAVE_CONFIG_H
# ../libdwarf gets us to local headers and a libdwarf 
# archive, usually, so we assume it.
DIRINC =        $(srcdir)/../libdwarf 
dwfwall =		-Wall
dwfsanitize =   
dwfzlib =       -lz
LIBS =		 -L../libdwarf -ldwarf -lelf $(dwfzlib)
INCLUDES =	-I. -I$(srcdir) -I../libdwarf -I$(srcdir)/../libdwarf
CFLAGS =	$(PREINCS) -g -O2 $(INCLUDES) $(dwfwall) $(dwfsanitize) -DCONFPREFIX=${libdir} $(POSTINCS)
LDFLAGS =	$(PRELIBS)  $(dwfsanitize) $(LIBS) $(POSTLIBS)
#VG =            valgrind --leak-check=full
VG =


INSTALL = cp

binprefix =

all: simplereader frame1

simplereader: $(srcdir)/simplereader.c $(srcdir)/../dwarfdump/naming.c $(srcdir)/../dwarfdump/helpertree.c $(srcdir)/../dwarfdump/dwarf_tsearchbal.c $(srcdir)/../dwarfdump/addrmap.c $(srcdir)/../dwarfdump/checkutil.c
	$(CC) $(CFLAGS) $(srcdir)/simplereader.c $(srcdir)/../dwarfdump/naming.c $(srcdir)/../dwarfdump/helpertree.c $(srcdir)/../dwarfdump/dwarf_tsearchbal.c $(srcdir)/../dwarfdump/addrmap.c $(srcdir)/../dwarfdump/checkutil.c -o simplereader $(LDFLAGS)

frame1: $(srcdir)/frame1.c
	$(CC) $(CFLAGS) $(srcdir)/frame1.c -o frame1 $(LDFLAGS)

get_dwarf_info: $(srcdir)/get_dwarf_info.c $(srcdir)/../dwarfdump/naming.c $(srcdir)/../dwarfdump/helpertree.c $(srcdir)/../dwarfdump/dwarf_tsearchbal.c $(srcdir)/../dwarfdump/addrmap.c $(srcdir)/../dwarfdump/checkutil.c
	$(CC) $(CFLAGS) $(srcdir)/get_dwarf_info.c $(srcdir)/../dwarfdump/naming.c $(srcdir)/../dwarfdump/helpertree.c $(srcdir)/../dwarfdump/dwarf_tsearchbal.c $(srcdir)/../dwarfdump/addrmap.c $(srcdir)/../dwarfdump/checkutil.c -o $@ $(LDFLAGS)

install: all
	echo do no install

uninstall:
	echo do no uninstall

clean:
	rm -f *.o
	rm -f frame1
	rm -f simplereader
	rm -f *~

distclean: clean
	rm -f config.log config.h config.cache config.status 
	rm -rf autom4te.cache
	rm -rf Makefile

shar:
	@echo "shar not set up yet"
dist:
	@echo "dist not set up yet"
