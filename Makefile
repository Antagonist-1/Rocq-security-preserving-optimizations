.PHONY: rocq clean

ROCQC=rocq compile
ROCQFLAGS=-R src ""

rocq:
	$(ROCQC) $(ROCQFLAGS) src/Map.v
	$(ROCQC) $(ROCQFLAGS) src/VarSets.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Syntax.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Security.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Semantics.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Main.v
	$(ROCQC) $(ROCQFLAGS) src/examples/Programs.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Optimizations.v
	$(ROCQC) $(ROCQFLAGS) src/proofs/SecEnvProofs.v
	$(ROCQC) $(ROCQFLAGS) src/proofs/SecurityProofs.v
	echo "Running Tests ..."
	@for file in src/examples/*.v; do \
		echo "Compiling $$file"; \
		$(ROCQC) $(ROCQFLAGS) "$$file"; \
	done


clean:
	rm -f src/*.vo* src/*.glob src/*.aux src/.*.aux src/.*.cache src/Language/*.vo* src/Language/*.glob src/Language/*.aux src/examples/*.vo* src/examples/*.glob src/examples/*.aux src/optimizations/*.vo* src/optimizations/*.glob src/optimizations/*.aux src/proofs/*.vo* src/proofs/*.glob src/proofs/*.aux
