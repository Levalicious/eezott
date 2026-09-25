<$MKROOT/$objtype/mkfile

TARG=eezott

OFILES=\
	main.$O\
	parse.$O\
	eval.$O\
	elab.$O\
	erase.$O\
	level.$O\
	meta.$O\

HFILES=\
	tt.h\
	../libeezo/types.h\
	../libeezo/bn.h\

CFLAGS=-g -O2 -Wall -I.

LIBS=../libeezo

<$MKROOT/proto/mkone

# relink when the library changes (mkone LIBS= links it but does not depend on it)
$PROG: ../libeezo/libeezo.a
