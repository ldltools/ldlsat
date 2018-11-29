#
SUBDIRS = grammar

all::
	for d in $(SUBDIRS); do $(MAKE) -C $$d $@ || exit 1; done

clean::;	rm -f *~ \#*
veryclean::	clean
install::
