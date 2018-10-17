FSTAR := fstar.exe --query_stats --__no_positivity --include /home/jay/everest/kremlin/kremlib/ --use_hints --record_hints --cache_checked_modules

# List of everything
all: DListLowInd

# Cleanup
cleanhints:
	rm -f *.hints

cleanchecked:
	rm -f *.checked

clean: cleanchecked
	@echo "Cleaned! Run [make nuke] to remove hints though."

nuke: cleanhints cleanchecked
	@echo "Nuked everything!"

# Generic Rule
%: %.fst
	$(FSTAR) $<
