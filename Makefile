all: DList.fst
	fstar --use_hints --record_hints --query_stats --include /home/jay/everest/kremlin/kremlib/ --__no_positivity DList.fst
