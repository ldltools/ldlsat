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
CAMLFIND_FLAGS	=
CAMLFIND_FLAGS	+= -package ppx_deriving.eq
CAMLFIND_FLAGS	+= -package ppx_deriving.ord
CAMLFIND_FLAGS	+= -package ppx_deriving.show
CAMLFIND_FLAGS	+= -package ppx_deriving_yojson

# on our own
CAML_INC_FLAGS	=
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/result
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/ppx_deriving
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/ppx_deriving_yojson
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/yojson
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/biniou
CAML_INC_FLAGS	+= -I $(OPAM_PREFIX)/lib/easy-format

CAMLCFLAGS	= $(CAMLFIND_FLAGS) $(CAML_INC_FLAGS)
CAMLOPTFLAGS	= $(CAMLFIND_FLAGS) $(CAML_INC_FLAGS)

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

FOR_PACK	= -for-pack Ldlsat

CMAS		=
#CMAS		+= nums.cma
CMAS		+= result.cma ppx_deriving_runtime.cma ppx_deriving_yojson_runtime.cma
CMAS		+= easy_format.cma biniou.cma yojson.cma

CMXAS		= $(CMAS:%.cma=%.cmxa)

BINS.byte	= ldl2mso.byte ldlsimp.byte
#BINS.byte	+= ldl2re.byte re2mso.byte
BINS.byte	+= ldl2afw.byte
#BINS.byte	+= afwprint.byte
#BINS.byte	+= afw2nfa.byte nfa2dfa.byte dfaprint.byte
#BINS.opt	+= $(BINS.byte:%.byte=%.opt)
BINS.opt	= ldl2mso.opt ldlsimp.opt
BINS		= $(BINS.byte:%=$(BUILD_DIR)/%) $(BINS.opt:%=$(BUILD_DIR)/%)

LIBS.byte	= ldlsat.cma
LIBS.byte	:= $(LIBS.byte:%=$(BUILD_DIR)/_export/%)
LIBS.opt	= ldlsat.cmxa
LIBS.opt	:= $(LIBS.opt:%=$(BUILD_DIR)/_export/%)
LIBS		= $(LIBS.byte) $(LIBS.opt) $(LIBS.opt:%.cmxa=%.a)

-include Makefile.common

all::	$(BINS)

# ldl2mso
$(BUILD_DIR)/ldl2mso.byte:	$(LIBS.byte) $(BUILD_DIR)/mso/ldl2mso_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $(LIBS.byte) $^
$(BUILD_DIR)/ldl2mso.opt:	$(LIBS.opt) $(BUILD_DIR)/mso/ldl2mso_main.cmx
	$(CAMLOPT) $(CAMLOPTFLAGS) -o $@ $(CMXAS) $^
$(BUILD_DIR)/mso/ldl2mso_main.cmo:	mso/ldl2mso_main.ml $(BUILD_DIR)/_export/ldlsat.cmi
	$(CAMLC) $(CAMLCFLAGS) -I $(BUILD_DIR)/_export -o $@ -c $<
$(BUILD_DIR)/mso/ldl2mso_main.cmx:	mso/ldl2mso_main.ml $(BUILD_DIR)/_export/ldlsat.cmi
	$(CAMLOPT) $(CAMLOPTFLAGS) -I $(BUILD_DIR)/_export -o $@ -c $<
# legacy
$(BUILD_DIR)/ldl2re.byte:	$(LIBS.byte) $(BUILD_DIR)/ldl2re_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^
$(BUILD_DIR)/re2mso.byte:	$(LIBS.byte) $(BUILD_DIR)/mso/re2mso_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^

# ldl2afw
$(BUILD_DIR)/ldl2afw.byte:	$(LIBS.byte) $(BUILD_DIR)/afw/ldl2afw_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $(LIBS.byte) $^
$(BUILD_DIR)/ldl2afw.opt:	$(LIBS.opt) $(BUILD_DIR)/afw/ldl2afw_main.cmx
	$(CAMLOPT) $(CAMLOPTFLAGS) -o $@ $(CMXAS) $^
$(BUILD_DIR)/afw/ldl2afw_main.cmo:	afw/ldl2afw_main.ml $(BUILD_DIR)/_export/ldlsat.cmi
	$(CAMLC) $(CAMLCFLAGS) -I $(BUILD_DIR)/_export -o $@ -c $<
$(BUILD_DIR)/afw/ldl2afw_main.cmx:	afw/ldl2afw_main.ml $(BUILD_DIR)/_export/ldlsat.cmi
	$(CAMLOPT) $(CAMLOPTFLAGS) -I $(BUILD_DIR)/_export -o $@ -c $<
# legacy
$(BUILD_DIR)/afwprint.byte:	$(LIBS.byte) $(BUILD_DIR)/afw/afwprint_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^

# ldlsimp
$(BUILD_DIR)/ldlsimp.byte:	$(LIBS.byte) $(BUILD_DIR)/ldlsimp_main.cmo
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CMAS) $^
$(BUILD_DIR)/ldlsimp.opt:	$(LIBS.opt) $(BUILD_DIR)/ldlsimp_main.cmx
	$(CAMLOPT) $(CAMLOPTFLAGS) -o $@ $(CMXAS) $^
$(BUILD_DIR)/ldlsimp_main.cmo:	ldlsimp_main.ml $(BUILD_DIR)/_export/ldlsat.cmi
	$(CAMLC) $(CAMLCFLAGS) -I $(BUILD_DIR)/_export -o $@ -c $<
$(BUILD_DIR)/ldlsimp_main.cmx:	ldlsimp_main.ml $(BUILD_DIR)/_export/ldlsat.cmx
	$(CAMLOPT) $(CAMLCFLAGS) -I $(BUILD_DIR)/_export -o $@ -c $<


all::	$(LIBS)

# ldlsat library (packed)
SRC_MODULES	=	ldl re mso/mso mso/re2mso afw/afw afw/ldl2afw
SRC_MODULES	+=	toysat ldlsimp
SRC_MODULES	+=	$(BUILD_DIR)/ldl_p ldl_l version
$(BUILD_DIR)/_export/ldlsat.mli:	$(SRC_MODULES:%=%.mli)
	mkdir -p $$(dirname $@)
	rm -f $@; touch $@
	for f in $^; do \
	  m=$$(basename $$f .mli); \
	  echo "module $${m^} : sig" >> $@; \
	  cat $$f >> $@; \
	  echo "end" >> $@; \
	done
$(BUILD_DIR)/_export/ldlsat.cmi:	$(BUILD_DIR)/_export/ldlsat.mli
	$(CAMLC) $(CAMLCFLAGS) -o $@ $<
$(BUILD_DIR)/_export/ldlsat.cmo:	$(CMOS) $(BUILD_DIR)/_export/ldlsat.cmi
	mkdir -p $$(dirname $@)
	$(CAMLC) $(CAMLCFLAGS) -o $@ -pack \
	$(BUILD_DIR)/{ldl,ldl_p,ldl_l,toysat,ldlsimp,re}.cmo \
	$(BUILD_DIR)/mso/{mso,re2mso}.cmo \
	$(BUILD_DIR)/afw/{afw,ldl2afw}.cmo \
	$(BUILD_DIR)/version.cmo
$(BUILD_DIR)/_export/ldlsat.cma:	$(BUILD_DIR)/_export/ldlsat.cmo
	$(CAMLC) -o $@ -a $<
$(BUILD_DIR)/_export/ldlsat.cmx:	$(CMXS) $(BUILD_DIR)/_export/ldlsat.cmi
	mkdir -p $$(dirname $@)
	$(CAMLOPT) $(CAMLOPTFLAGS) -o $@ -pack \
	$(BUILD_DIR)/{ldl,ldl_p,ldl_l,toysat,ldlsimp,re}.cmx \
	$(BUILD_DIR)/mso/{mso,re2mso}.cmx \
	$(BUILD_DIR)/afw/{afw,ldl2afw}.cmx \
	$(BUILD_DIR)/version.cmx
$(BUILD_DIR)/_export/ldlsat.cmxa:	$(BUILD_DIR)/_export/ldlsat.cmx
	$(CAMLOPT) -o $@ -a $<

# lexer/parser
$(BUILD_DIR)/ldl_p.cmi: $(BUILD_DIR)/ldl.cmi
$(BUILD_DIR)/ldl_p.cmo: $(BUILD_DIR)/ldl.cmi $(BUILD_DIR)/ldl_p.cmi
$(BUILD_DIR)/ldl_p.cmx: $(BUILD_DIR)/ldl.cmi $(BUILD_DIR)/ldl_p.cmi
$(BUILD_DIR)/ldl_l.cmi: $(BUILD_DIR)/ldl_p.cmi

#
install::	all install_bins install_libs

install_bins::	all
	mkdir -p $(PREFIX)/bin
#	rsync -avzop $(BINS) $(PREFIX)/bin/
	rsync -avzop $(BUILD_DIR)/ldl2mso.opt $(PREFIX)/bin/ldl2mso
	rsync -avzop $(BUILD_DIR)/ldlsimp.opt $(PREFIX)/bin/ldlsimp
install_libs::	all
	mkdir -p $(PREFIX)/lib/ldlsat
#	rsync -avzop $(LIBS) $(PREFIX)/lib/ldlsat
#	rsync -avzop $(CMIS) $(PREFIX)/lib/ldlsat
#	rsync -avzop $(SRCS_mli) $(PREFIX)/lib/ldlsat
	rsync -avzop $(BUILD_DIR)/_export/ldlsat.{mli,cmi,cma,cmxa,a} $(PREFIX)/lib/ldlsat

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

$(BUILD_DIR)/ppx:
	$(CAMLOPT) $(CAML_INC_FLAGS) \
	-I $(HOME)/.opam/system/lib/ppx_driver \
	-I $(HOME)/.opam/system/lib/ppx_core \
	-I $(HOME)/.opam/system/lib/ppx_optcomp \
	-predicates ppx_driver -o $@ -linkpkg \
	-package ppx_deriving -package ppx_deriving.show -package ppx_deriving_yojson \
	{ppx_deriving_runtime,ppx_deriving_yojson_runtime}.cmxa \
	{ppx_core,ppx_optcomp,ppx_driver,ppx_driver_runner}.cmxa
