(** Core set of utility functions that might be nice to get included
    into ulib *)
module Utils

(** For lists *)
module T = FStar.List.Tot
module P =  FStar.List.Pure
open FStar.List.Tot
open FStar.List.Pure

let rec lemma_index_fst_unsnoc (#t:Type) (l:list t) (i:nat) :
  Lemma
    (requires (length l > 0 /\ i < length l - 1))
    (ensures (i < length (fst (unsnoc l)) /\ index (fst (unsnoc l)) i == index l i)) =
  T.lemma_unsnoc_index l i
