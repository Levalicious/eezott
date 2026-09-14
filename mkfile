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
	bn.$O\

HFILES=\
	tt.h\
	bn.h\
	../libeezo/types.h\

CFLAGS=-g -O2 -Wall -I.

<$MKROOT/proto/mkone
