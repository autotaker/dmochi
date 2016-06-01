.PHONY: clean
hcsolver: main.ml myLexer.ml myParser.ml
	ocamlfind ocamlopt -package fpat -linkpkg -o $@ myParser.mli myParser.ml myLexer.ml main.ml

myLexer.ml: myLexer.mll
	ocamllex myLexer.mll

myParser.ml: myParser.mly
	ocamlyacc myParser.mly

clean:
	rm -f *.o *.cmi *.cmo *.cmx *.o myLexer.ml myParser.mli myParser.ml hcsolver

