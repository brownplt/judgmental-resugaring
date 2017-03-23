COMPILE=./node_modules/bs-platform/bin/bsc.exe

all:
	$(COMPILE) Util.ml
	$(COMPILE) Term.ml
	$(COMPILE) Grammar.ml
	ocamllex parser/Lexer.mll
	ocamlyacc parser/Parser.mly
	cp parser/*.ml .
	cp parser/*.mli .
	$(COMPILE) Parser.mli
	$(COMPILE) Parser.ml
	$(COMPILE) Lexer.ml
	$(COMPILE) Parse.ml
	$(COMPILE) -bs-main test.ml

clean:
	rm *.js
	rm *.cmi
	rm *.cmj

.PHONY: parser
