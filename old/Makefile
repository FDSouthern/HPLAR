# List of ML files to compile as a library. This leaves out the following
# which are probably not much use:
#
# sigma.ml       (Sigma-formulas and evaluator-by-proof)
# turing.ml      (OCaml implementation of Turing machines)
# undecidable.ml (Proofs related to undecidability results)
# bhk.ml         (Trivial instance of BHK interpretation)
# many.ml        (Example relevant to many-sorted logic)
# hol.ml         (Simple higher order logic setup)

MLFILES = lib.ml intro.ml formulas.ml prop.ml propexamples.ml           \
          defcnf.ml dp.ml stal.ml bdd.ml fol.ml skolem.ml               \
          herbrand.ml unif.ml tableaux.ml resolution.ml prolog.ml       \
          meson.ml skolems.ml equal.ml cong.ml rewrite.ml               \
          order.ml completion.ml orewrite.ml eqelim.ml                  \
          paramodulation.ml decidable.ml qelim.ml cooper.ml             \
          complex.ml grobner.ml real.ml geom.ml interpolation.ml        \
          combining.ml transition.ml temporal.ml model.ml ltl.ml        \
          ste.ml lcf.ml hilbert.ml lcfprop.ml lcffol.ml checking.ml     \
          tactics.ml

# The default is to build a bytecode executable

bytecode: example.ml atp.cmo; ocamlc -pp "camlp4o ./Quotexpander.cmo" -o example nums.cma atp.cmo example.ml

# Alternatively, produce native code

compiled: example.ml atp.cmx; ocamlopt -pp "camlp4o ./Quotexpander.cmo" -o example nums.cmxa atp.cmx example.ml

# Make the appropriate object for the main body of code

atp.cmx: Quotexpander.cmo atp.ml; ocamlopt -pp "camlp4o ./Quotexpander.cmo" -w ax -c atp.ml

atp.cmo: Quotexpander.cmo atp.ml; ocamlc -pp "camlp4o ./Quotexpander.cmo" -w ax -c atp.ml

# Make the camlp4 quotation expander

Quotexpander.cmo: Quotexpander.ml; ocamlc -I +camlp4 -c Quotexpander.ml

# Extract the non-interactive part of the code

atp.ml: $(MLFILES); ./Mk_ml_file $(MLFILES) >atp.ml

# Clean up

clean:; -rm -f atp.cma atp.cmi atp.cmo atp.cmx atp.o atp.ml example example.cmi example.cmo example.cmx example.o Quotexpander.cmo Quotexpander.cmi
