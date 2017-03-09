COMPILE=./node_modules/bs-platform/bin/bsc.exe

all:
	$(COMPILE) -bs-main test.ml

parser:
	ocamllex parser/Lexer.mll
	ocamlyacc parser/Parser.mly
	cp parser/*.ml .
	cp parser/*.mli .
	$(COMPILE) Parse.ml

clean:
	rm *.js
	rm *.cmi
	rm *.cmj

.PHONY: parser
