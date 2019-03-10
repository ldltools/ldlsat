all::

list:
	@for f in $(shell echo *.ldl); do \
	echo -ne "`basename $$f .ldl`\t"; grep -v '^/' $$f;\
	done

test:
	shelltest valid.conf

clean::
	rm -f *~
