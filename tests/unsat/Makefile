all::

list:
	@for f in $(shell echo *.ldl); do \
	echo -ne "`basename $$f .ldl`\t"; grep -v '^/' $$f;\
	done

test:
	shelltest unsat.conf

clean::
	rm -f *~
