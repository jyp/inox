# This short Makefile generates the necessary files for the
# compilation of Inox

BNFCSOURCEFILES:=$(shell find Bnf/ -name "*.cf" | xargs basename -a)
BNFCFILES=$(BNFCSOURCEFILES:%.cf=Bnf/%/Abs.hs) $(BNFCSOURCEFILES:%.cf=Bnf/%/Lex.hs) $(BNFCSOURCEFILES:%.cf=Bnf/%/Par.hs)

# BNFC grammar generation
Bnf/%/Abs.hs: Bnf/%.cf
	bnfc -p Bnf -d $?
Bnf/%/Lex.x: Bnf/Abs%.hs
Bnf/%/Par.y: Bnf/Abs%.hs

# Generate lexer with alex
%.hs: %.x
	alex $?

# Generate parser with happy
%.hs: %.y
	happy $?

all: $(BNFCFILES)
	cabal new-build

.PHONY: all NOARG
.NOARG: all
