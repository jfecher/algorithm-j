.PHONY: clean

j: Makefile parser.cmo lexer.cmo j.ml
	ocamlc -o j parser.ml lexer.ml j.ml

parser.cmo: Makefile parser.mly expr.mli
	menhir parser.mly
	ocamlc expr.mli
	ocamlc parser.mli

lexer.cmo: Makefile parser.cmo lexer.mll
	ocamllex lexer.mll
	ocamlc -c -i lexer.ml > lexer.mli
	ocamlc lexer.mli

clean:
	@rm *.cmo *.cmi lexer.ml lexer.mli parser.ml parser.mli j
