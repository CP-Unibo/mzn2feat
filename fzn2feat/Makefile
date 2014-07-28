EXEEXT=

EXE_FILE = 	fzn2feat$(EXEEXT)
SRC =	        
OBJ = 		flatzinc.tab.o
GENCFILES = 	flatzinc.tab.c lex.yy.c
OTHER = 	flatzinc.output 

# NOTE: we need to pass the `-l' flag to ensure the scanner internal
# variable `yylineno' is available.
#
LEX =		flex
LEXFLAGS =      -l
LEXLIB =	

YACC =		bison
YACCFLAGS =	-v

CC =		g++	
CFLAGS =	-g -O
RM =		/bin/rm -f

$(EXE_FILE):	$(OBJ)
		$(CC) $(CFLAGS) -o $(EXE_FILE) $(OBJ) $(LEXLIB)
		cp $(EXE_FILE) $(MZN2FEAT_HOME)/bin

flatzinc.tab.c:	flatzinc.y lex.yy.c static_features.cc expr.cc
		$(YACC) $(YACCFLAGS) flatzinc.y

lex.yy.c:	flatzinc.l
		$(LEX) $(LEXFLAGS) flatzinc.l
			
clean:
		$(RM) $(OBJ) $(GENCFILES) $(OTHER) $(EXE_FILE) core static_features.o expr.o

clobber:	clean
		$(RM) $(EXE_FILE)

.PHONY: distclean
distclean: clobber
