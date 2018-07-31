# $Id: Makefile,v 1.1 2018/01/10 03:52:34 sato Exp $

usage:
	@echo "usage: make <target>"
	@echo "where <target> can be one of the following"
	@echo -e "\tlist\tshow the test cases in this directory"
	@echo -e "\ttest\trun regression tests"
	@echo -e "\tdfa\tgenerate DFA files (in ./out)"
#	@echo -e "\tafw\tgenerate AFW files (in ./out)"

list:
	@for f in $(TESTCASES_LDL); do echo -ne "`basename $$f .ldl`\t" | cat - $$f; done

TOP_DIR		= $(shell readlink -f ..)
include ./Makefile.common

# LDL -> MSO
out/%.mso:	%.ldl
	@mkdir -p $(dir $@)
	@test -x $(LDL2MSO) || exit 1
	$(LDL2MSO) $< -o $@ || { rm -f $@; exit 1; }
# LDL -> AFW
out/%.afw:	%.ldl
	@mkdir -p $(dir $@)
	@test -x $(LDL2AFW) || exit 1
	$(LDL2AFW) $< -o $@ || { rm -f $@; exit 1; }

.PRECIOUS:	out/%.re out/%.mso out/%.afw

TESTCASES_LDL	= $(shell echo test??.ldl valid/*.ldl unsat/*.ldl)
TESTCASES_DFA	= $(TESTCASES_LDL:%.ldl=out/%.mso.png)
TESTCASES_AFW	= $(TESTCASES_LDL:%.ldl=out/%.afw.png)

dfa:	$(TESTCASES_DFA)
afw:	$(TESTCASES_AFW)

test:	dfa
	python3 check.py

all::
install::
clean::
	find . -name '*~' | xargs rm -f
veryclean::	clean
	rm -rf out/*
