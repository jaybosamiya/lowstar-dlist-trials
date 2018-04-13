FSTAR=$(FSTAR_HOME)/bin/fstar.exe --query_stats --__no_positivity
FSTARK=$(FSTAR) --include $(KRML_HOME)/kremlib/

.PHONY: all ref low genhintref genhintlow nohintref nohintlow

all:
	@echo "Usage:"
	@echo "  make {ref|low}"
	@echo "  make genhint{ref|low}"
	@echo "  make nohint{ref|low}"

ref: DListRef.fst DListRef.fst.hints
	$(FSTAR) --use_hints --detail_hint_replay $<

low: DListLow.fst DListRef.fst.hints
	$(FSTARK) --use_hints --detail_hint_replay $<

genhintref: DListRef.fst
	$(FSTAR) --record_hints $<

genhintlow: DListLow.fst
	$(FSTARK) --record_hints $<

nohintref: DListRef.fst
	$(FSTAR) $<

nohintlow: DListLow.fst
	$(FSTARK) $<
