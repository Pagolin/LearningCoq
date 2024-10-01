
.PHONY: deps
deps:
	coqdep . *v | coqgraph - | dot -Tpdf > dependencies.pdf

.PHONY: TAGS
TAGS:
	coqtags *.v

.PHONY: clean
clean:
	rm -f *.vo *.glob *.vio *.vos *.vok .*.aux *.stat
	rm -f $(TOCLEAN)

