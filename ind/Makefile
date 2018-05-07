FSTAR := fstar.exe --query_stats --__no_positivity --include /home/jay/everest/kremlin/kremlib/ --use_hints --cache_checked_modules

# List of everything
all: Gpointers DListLowInd Utils

# Dependencies
DListLowInd: Utils Gpointers

# Generic Rule
%: %.fst
	$(FSTAR) $<
