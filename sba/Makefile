CFLAGS=-g -O3
all: gb
gb: prime.o gb.o ff.o z.o q.o y.tab.o
	cc -g -o gb prime.o gb.o z.o q.o ff.o y.tab.o -lgc -lgmp
y.tab.c: parse.y
	yacc -d parse.y
clean:
	rm -f gb *.o y.tab.*
