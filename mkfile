<$MKROOT/$objtype/mkfile

TARG=eezott

OFILES=\
	main.$O\
	parse.$O\
	eval.$O\
	elab.$O\
	erase.$O\
	agda.$O\
	ctt.$O\
	level.$O\
	meta.$O\

HFILES=\
	tt.h\
	machine.h\
	../libeezo/types.h\
	../libeezo/bn.h\


CFLAGS=-g -O2 -Wall -I. -I..
LIBEEZO=../libeezo/libeezo.a
LIBFILES=$LIBEEZO

<$MKROOT/proto/mkone

# the library, a real prerequisite of the program: built in its directory when its sources change (mkone LIBFILES)
$LIBEEZO: `ls ../libeezo/*.[ch]`
	cd ../libeezo && mk libeezo.a

