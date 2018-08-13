#

#PREFIX		?= _build/install
PREFIX		?= /usr/local
SUBDIRS		= src scripts tests docs

all::
	for d in $(SUBDIRS); do make -C $$d $@ || exit 1; done

install::
	@test -d $(PREFIX)/bin || mkdir -p $(PREFIX)/bin
	for d in $(SUBDIRS); do make -C $$d PREFIX=$(PREFIX) $@; done

clean::
	find . -name '#*' -or -name '*~' | xargs rm -f
	for d in $(SUBDIRS); do make -C $$d $@; done

veryclean::	clean
	for d in $(SUBDIRS); do make -C $$d $@; done
	rm -rf _build/*

#
GITHOME ?= $(HOME)/git/github.com/ldltools/ldlsat
rsync::	clean
	test -d $(GITHOME) || exit 1
	rsync -avzop --exclude=_build --exclude=.git --exclude=out --exclude=obsolete ./ $(GITHOME)
tar:	veryclean
	(dir=`basename $$PWD`; cd ..; tar cvJf dsl4sc`date +%y%m%d`.tar.xz --exclude=.git --exclude=_build --exclude=RCS --exclude=obsolete $$dir)

# docker
docker_build:
	docker build -t "ldltools/ldlsat" .
docker_run:
	docker run -it "ldltools/ldlsat"
