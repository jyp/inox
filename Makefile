# This short Makefile generates the necessary files for the
# compilation of Inox

BNFCSOURCEFILES:=$(shell find Bnf/ -name "*.cf" | xargs basename -a)
BNFCFILES=$(BNFCSOURCEFILES:%.cf=Bnf/Abs%.hs) $(BNFCSOURCEFILES:%.cf=Bnf/Lex%.hs) $(BNFCSOURCEFILES:%.cf=Bnf/Par%.hs)

# BNFC grammar generation
Bnf/Abs%.hs: Bnf/%.cf
	cd Bnf; bnfc $(?F) ;cd ..

# Generate
%.hs: %.x
	alex $?

%.hs: %.y
	happy $?

all: $(BNFCFILES)
	stack build

.PHONY: all NOARG
.NOARG: all
