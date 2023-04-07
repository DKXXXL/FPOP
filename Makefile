ifeq "$(COQBIN)" ""
  COQBIN=$(dir $(shell which coqtop))/
endif

%: Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

tests: all
	@$(MAKE) -C tests -s clean
	@$(MAKE) -C tests -s all

-include Makefile.coq

clean::
	rm -f ./theories/.*.aux
	rm -f ./showcase_test/*.vo
	rm -f ./showcase_test/*.glob
	rm -f ./showcase_test/*.aux
	rm -f ./showcase_test/.*.aux
	rm -f ./showcase_test/*.vos
	rm -f ./showcase_test/*.vok

# clean::
# 	rm -f Makefile.coq Makefile.coq.bak Makefile.coq.conf
