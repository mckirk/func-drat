srcdir = src/

RESULT = funcdrat
SOURCES = $(srcdir)misc.ml $(srcdir)flatArray.ml $(srcdir)types.ml $(srcdir)state.ml $(srcdir)main.ml
PACKS = batteries

opt: OCAMLNCFLAGS := -O3 -unboxed-types
opt: nc

noinl: OCAMLNCFLAGS := -inline 0
noinl: nc

deb: PPFLAGS := -D DEBUG -D BACKTRACE -D VERBOSE -D ASSERTS
deb: dc

verb: PPFLAGS := -D VERBOSE
verb: nc

asserts: PPFLAGS := -D BACKTRACE -D ASSERTS
asserts: nc

bt: PPFLAGS := -D BACKTRACE
bt: nc
  
OCAMLMAKEFILE = OCamlMakefile
include $(OCAMLMAKEFILE)
