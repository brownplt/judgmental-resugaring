COMPILE=./node_modules/bs-platform/bin/bsc.exe
COMPILE_OCAML=ocamlc

all:
	$(COMPILE) Util.ml
	$(COMPILE) Term.ml
	$(COMPILE) Grammar.ml
	$(COMPILE) Desugar.ml
	$(COMPILE) Judgment.ml
	ocamllex parser/Lexer.mll
	ocamlyacc parser/Parser.mly
	cp parser/*.ml .
	cp parser/*.mli .
	$(COMPILE) Parser.mli
	$(COMPILE) Parser.ml
	$(COMPILE) Lexer.ml
	$(COMPILE) Parse.ml
	$(COMPILE) Fresh.mli
	$(COMPILE) Fresh.ml
	$(COMPILE) Infer.mli
	$(COMPILE) Infer.ml
	$(COMPILE) TestRunner.mli
	$(COMPILE) TestRunner.ml
	$(COMPILE) test.ml
	node test.js

ocaml:
	$(COMPILE_OCAML) -g -o test Util.ml Term.ml Grammar.ml Desugar.ml Judgment.ml Parser.mli Parser.ml Lexer.ml Parse.ml Fresh.mli Fresh.ml Infer.mli Infer.ml TestRunner.mli TestRunner.ml test.ml

clean:
	rm *.js
	rm *.cmi
	rm *.cmj

.PHONY: parser
