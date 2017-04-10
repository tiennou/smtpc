# $Cambridge: hermes/src/smtpc/Makefile,v 1.8 2006/09/15 12:16:20 fanf2 Exp $

all: 	smtpc

clean:
	rm -rf smtpc smtpc-*

dist: ChangeLog
	version=`awk '/Cambridge/ { print $$3 }' main.c`;	\
	dir=smtpc-$$version; tar=$$dir.tar.gz;			\
	rm -rf $$dir $$tar;					\
	mkdir $$dir;						\
	cp ChangeLog Makefile main.c $$dir;			\
	tar cfz $$tar $$dir;					\
	rm -rf $$dir;

ChangeLog: main.c Makefile
	cvslog > ChangeLog

smtpc: main.c
	gcc -o smtpc main.c -lssl -lcrypto || (			\
		echo '***' trying alternate build....;		\
		gcc -o smtpc main.c -lssl -lcrypto -lresolv )
