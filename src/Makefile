# -*-Makefile-*-
# $Id: $

all::

TOP_DIR		= $(shell readlink -f ..)
BUILD_DIR	= $(TOP_DIR)/_build/caml
PREFIX		?= $(TOP_DIR)/_build/install
#SRC_DIRS	= .

OPAM_PREFIX	= $(shell opam config var prefix)
OCAMLFIND	= $(OPAM_PREFIX)/bin/ocamlfind
CAMLC		= $(OCAMLFIND) ocamlc
CAMLOPT		= $(OCAMLFIND) ocamlopt

ifdef PROF
#CAMLC		:= $(OCAMLFIND) ocamlcp
#CAMLOPT	:= $(OCAMLFIND) ocamloptp
endif

# for ocamlfind
CAML_PKG_PLAGS	=
CAML_PKG_FLAGS	+= -package ppx_deriving.eq
CAML_PKG_FLAGS	+= -package ppx_deriving.ord
CAML_PKG_FLAGS	+= -package ppx_deriving.show
CAML_PKG_FLAGS	+= -package ppx_deriving_yojson
#CAML_PKG_FLAGS	+= -package bigstring
#CAML_PKG_FLAGS	+= -package sexplib
#CAML_PKG_FLAGS	+= -package ppx_sexp_conv

# on our own
CAML_INC_FLAGS	=
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/result
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/ppx_deriving
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/ppx_deriving_yojson
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/yojson
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/biniou
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/easy-format
#CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/bigstring
#CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/sexplib
#CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/ppx_sexp_conv
#CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/xml-light

CAMLCFLAGS	= $(CAML_INC_FLAGS) $(CAML_PKG_FLAGS)
CAMLOPTFLAGS	= $(CAML_INC_FLAGS) $(CAML_PKG_FLAGS)

CAMLCFLAGS	+= -unsafe-string
CAMLOPTFLAGS	+= -unsafe-string

ifdef DEBUG
CAMLCFLAGS	+= -g -w +A
CAMLOPTFLAGS	+= -g -w +A
else
CAMLCFLAGS	+= -noassert -w -A
CAMLOPTFLAGS	+= -noassert -w -A
endif

ifdef PROF
#CAMLCFLAGS	+= -p a
CAMLOPTFLAGS	+= -p
endif

CMAS		=
#CMAS		+= nums.cma
CMAS		+= result.cma ppx_deriving_runtime.cma ppx_deriving_yojson_runtime.cma
CMAS		+= easy_format.cma biniou.cma yojson.cma
#CMAS		+= unix.cma bigarray.cma bigstring.cma sexplib.cma
#CMAS		+= ppx_sexp_conv_expander.cma ppx_sexp_conv.cma
#CMAS		+= xml-light.cma

CMXAS		= $(CMAS:%.cma=%.cmxa)

-include Makefile.common

BINS.byte	= ldl2mso.byte ldlsimp.byte
BINS.byte	+= ldl2re.byte re2mso.byte
BINS.byte	+= ldl2afw.byte
BINS.byte	+= afwprint.byte
#BINS.byte	+= afw2nfa.byte nfa2dfa.byte dfaprint.byte
#BINS.opt	+= $(BINS.byte:%.byte=%.opt)
BINS.opt	= ldl2mso.opt ldlsimp.opt
BINS		= $(BINS.byte:%=$(BUILD_DIR)/%) $(BINS.opt:%=$(BUILD_DIR)/%)

LIBS.byte	= ldlsat.cma
LIBS.byte	:= $(LIBS.byte:%=$(BUILD_DIR)/%)
LIBS.opt	= ldlsat.cmxa
LIBS.opt	:= $(LIBS.opt:%=$(BUILD_DIR)/%)
LIBS		= $(LIBS.byte) $(LIBS.opt) $(LIBS.opt:%.cmxa=%.a)

all::	$(LIBS) $(BINS)

$(BUILD_DIR)/ldlsat.cma:	$(CMOS)
	$(CAMLC) $(CAMLCFLAGS) -o $@ -a \
	$(BUILD_DIR)/{ldl,ldl_l,ldl_p,toysat,ldlsimp,re}.cmo \
	$(BUILD_DIR)/mso/{mso,re2mso}.cmo \
	$(BUILD_DIR)/afw/{afw,ldl2afw}.cmo
$(BUILD_DIR)/ldlsat.cmxa:	$(CMXS)
	$(CAMLOPT) $(CAMLOPTFLAGS) -o $@ -a \
	$(BUILD_DIR)/{ldl,ldl_l,ldl_p,toysat,ldlsimp,re}.cmx \
	$(BUILD_DIR)/mso/{mso,re2mso}.cmx \
	$(BUILD_DIR)/afw/{afw,ldl2afw}.cmx

# $(BINS.byte)
$(BUILD_DIR)/ldl2mso.byte:	$(LIBS.byte) $(BUILD_DIR)/version.cmo $(BUILD_DIR)/mso/ldl2mso_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^
$(BUILD_DIR)/ldlsimp.byte:	$(LIBS.byte) $(BUILD_DIR)/version.cmo $(BUILD_DIR)/ldlsimp_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^

# legacy
$(BUILD_DIR)/ldl2re.byte:	$(LIBS.byte) $(BUILD_DIR)/ldl2re_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^
$(BUILD_DIR)/re2mso.byte:	$(LIBS.byte) $(BUILD_DIR)/mso/re2mso_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^
$(BUILD_DIR)/ldl2afw.byte:	$(LIBS.byte) $(BUILD_DIR)/afw/ldl2afw_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^
$(BUILD_DIR)/afwprint.byte:	$(LIBS.byte) $(BUILD_DIR)/afw/afwprint_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^

# $(BINS.opt)
$(BUILD_DIR)/ldl2mso.opt:	$(LIBS.opt) $(BUILD_DIR)/version.cmx $(BUILD_DIR)/mso/ldl2mso_main.cmx
	$(CAMLOPT) $(CAMLOPTFLAGS) -o $@ $(CMXAS) $^
$(BUILD_DIR)/ldlsimp.opt:	$(LIBS.opt) $(BUILD_DIR)/version.cmx $(BUILD_DIR)/ldlsimp_main.cmx
	$(CAMLOPT) $(CAMLOPTFLAGS) -o $@ $(CMXAS) $^

#
install::	all install_bins install_libs

install_bins::	all
	mkdir -p $(PREFIX)/bin
#	rsync -avzop $(BINS) $(PREFIX)/bin/
	rsync -avzop $(BUILD_DIR)/ldl2mso.opt $(PREFIX)/bin/ldl2mso
	rsync -avzop $(BUILD_DIR)/ldlsimp.opt $(PREFIX)/bin/ldlsimp
install_libs::	all
	mkdir -p $(PREFIX)/lib/ldlsat
	rsync -avzop $(LIBS) $(PREFIX)/lib/ldlsat
	rsync -avzop $(CMIS) $(PREFIX)/lib/ldlsat
	rsync -avzop $(SRCS_mli) $(PREFIX)/lib/ldlsat

clean::
veryclean::

ci::
	for d in `find . -type d`; do \
	  test -d $$d/RCS || continue;\
	  (cd $$d; echo *.ml* | xargs ci -m.);\
	done

Makefile.depend::	$(SRCS_mli) $(SRCS_ml) $(SRCS_mll) $(SRCS_mly)
	@n=0; missing=0;\
	while test $$n -lt 10; do \
	 test -s Makefile.depend || { sleep 1s; continue; };\
	 grep -q '^# generated at' Makefile.depend || { sleep 1s; continue; };\
	 line=`tail -1 Makefile.depend | grep '^# generated at'`;\
	 test ."$$line" = . && exit 0;\
	 break;\
	done
	echo "$(BUILD_DIR)/ldl_p.cmi: $(BUILD_DIR)/ldl.cmi" >> $@
	echo "$(BUILD_DIR)/ldl_l.cmi: $(BUILD_DIR)/ldl_p.cmi" >> $@
	echo "$(BUILD_DIR)/ldl_p.cmo: $(BUILD_DIR)/ldl.cmi $(BUILD_DIR)/ldl_p.cmi $(BUILD_DIR)/ldl_l.cmi" >> $@;\
	echo "$(BUILD_DIR)/ldl_p.cmx: $(BUILD_DIR)/ldl.cmi $(BUILD_DIR)/ldl_p.cmi $(BUILD_DIR)/ldl_l.cmi" >> $@;\

$(BUILD_DIR)/ppx:
	$(CAMLOPT) $(CAML_INC_FLAGS) \
	-I $(HOME)/.opam/system/lib/ppx_driver \
	-I $(HOME)/.opam/system/lib/ppx_core \
	-I $(HOME)/.opam/system/lib/ppx_optcomp \
	-predicates ppx_driver -o $@ -linkpkg \
	-package ppx_deriving -package ppx_deriving.show -package ppx_deriving_yojson \
	{ppx_deriving_runtime,ppx_deriving_yojson_runtime}.cmxa \
	{ppx_core,ppx_optcomp,ppx_driver,ppx_driver_runner}.cmxa
