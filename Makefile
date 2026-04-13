.PHONY: rocq clean

ROCQC=rocq compile
ROCQFLAGS=-R src ""

rocq:
	$(ROCQC) $(ROCQFLAGS) src/Map.v
	$(ROCQC) $(ROCQFLAGS) src/Language.v
# 	$(ROCQC) src/Lab06Signature.v
# 	$(ROCQC) src/Lab06Implementation.v

clean:
	rm -f src/*.vo* src/*.glob src/*.aux src/.*.aux src/.*.cache
