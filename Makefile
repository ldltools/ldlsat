#

#PREFIX		?= _build/install
PREFIX		?= /usr/local
SUBDIRS		= src scripts tests docs

all::
	for d in $(SUBDIRS); do $(MAKE) -C $$d $@ || exit 1; done

install::
	@test -d $(PREFIX)/bin || mkdir -p $(PREFIX)/bin
	for d in $(SUBDIRS); do $(MAKE) -C $$d PREFIX=$(PREFIX) $@; done

clean::
	find . -name '#*' -or -name '*~' | xargs rm -f
	for d in $(SUBDIRS); do $(MAKE) -C $$d $@; done

veryclean::	clean
	for d in $(SUBDIRS); do $(MAKE) -C $$d $@; done
	rm -rf _build

tar:	veryclean
	(dir=`basename $$PWD`; cd ..; tar cvJf ldlsat`date +%y%m%d`.tar.xz --exclude=.git --exclude=_build --exclude=RCS --exclude=obsolete --exclude=tests/ltl $$dir)

# docker
DOCKER_IMAGE	= ldltools/ldlsat
$(DOCKER_IMAGE)-dev:
	docker images | grep -q "^$@ " && { echo "$@ exists"; exit 0; } ||\
	docker build --target builder -t $@ .
$(DOCKER_IMAGE):
	docker images | grep -q "^$@ " && { echo "$@ exists"; exit 0; } ||\
	docker build -t $@ .

docker-build-all:	$(DOCKER_IMAGE)-dev $(DOCKER_IMAGE)
docker-build:	$(DOCKER_IMAGE)
docker-run:	$(DOCKER_IMAGE)
	docker run -it --rm $<
