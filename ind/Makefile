FSTAR := fstar.exe --query_stats --use_hints --record_hints --cache_checked_modules

# List of everything
all: DoublyLinkedList DoublyLinkedListIface iDoublyLinkedListIface

# Cleanup
cleanhints:
	rm -f *.hints

cleanchecked:
	rm -f *.checked

clean: cleanchecked
	@echo "Cleaned! Run [make nuke] to remove hints though."

nuke: cleanhints cleanchecked
	@echo "Nuked everything!"

# Generic Rules
%: %.fst
	$(FSTAR) $<

i%: %.fsti
	$(FSTAR) $<
