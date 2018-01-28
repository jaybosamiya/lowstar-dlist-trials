all: DList.fst
	fstar --query_stats --detail_errors --include /home/jay/everest/kremlin/kremlib/ --__no_positivity DList.fst
hints:
	fstar --use_hints --record_hints --query_stats --include /home/jay/everest/kremlin/kremlib/ --__no_positivity DList.fst
