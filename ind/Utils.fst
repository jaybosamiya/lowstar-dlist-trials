(** Core set of utility functions that might be nice to get included
    into ulib *)
module Utils

(** For lists *)
module T = FStar.List.Tot
module P =  FStar.List.Pure
open FStar.List.Tot
open FStar.List.Pure

let rec lemma_last_append (#t:Type) (l1 l2:list t) :
  Lemma
    (requires (length l2 > 0))
    (ensures (last (l1 @ l2) == last l2)) =
  T.lemma_append_last l1 l2

let rec lemma_unsnoc_append (#t:Type) (l1 l2:list t) :
  Lemma
    (requires (length l2 > 0)) // the [length l2 = 0] is trivial
    (ensures (
        let as, a = unsnoc (l1 @ l2) in
        let bs, b = unsnoc l2 in
        as == l1 @ bs /\ a == b)) =
  T.lemma_unsnoc_append l1 l2

let rec lemma_unsnoc_is_last (#t:Type) (l:list t) :
  Lemma
    (requires (length l > 0))
    (ensures (snd (unsnoc l) == last l /\ snd (unsnoc l) == index l (length l - 1))) =
  T.lemma_unsnoc_is_last l

let rec split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (list t * list t) =
  T.split_using l x

let rec lemma_split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  Lemma
    (ensures (
        let l1, l2 = split_using l x in
        (length l2 > 0) /\
        ~(x `memP` l1) /\ (hd l2 == x) /\
        append l1 l2 == l)) =
  T.lemma_split_using l x

let rec lemma_index_fst_unsnoc (#t:Type) (l:list t) (i:nat) :
  Lemma
    (requires (length l > 0 /\ i < length l - 1))
    (ensures (i < length (fst (unsnoc l)) /\ index (fst (unsnoc l)) i == index l i)) =
  T.lemma_unsnoc_index l i

let rec lemma_splitAt_append (#t:Type) (l1 l2:list t) :
  Lemma
    (ensures (splitAt (length l1) (append l1 l2) == (l1, l2))) =
  P.lemma_append_splitAt l1 l2

let rec index_of (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (i:nat{i < length l /\ index l i == x}) =
  T.index_of l x

let rec lemma_hd_r_split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (let a, b, c = split3 l i in
              length c > 0 ==> i + 1 < length l /\ hd c == index l (i + 1))) =
  P.lemma_split3_r_hd l i

let rec lemma_indexed_implies_memP (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (index l i `memP` l))
    [SMTPat (index l i `memP` l)] =
  T.lemma_index_memP l i

let rec lemma_splitAt_reindex_left (#t:Type) (i:nat) (l:list t) (j:nat) :
  Lemma
    (requires i <= length l /\ j < i)
    (ensures (
        let left, right = splitAt i l in
        lemma_splitAt l left right i;
        j < length left /\ index left j == index l j)) =
  P.lemma_splitAt_reindex_left i l j

let rec lemma_splitAt_reindex_right (#t:Type) (i:nat) (l:list t) (j:nat) :
  Lemma
    (requires i <= length l /\ j + i < length l)
    (ensures (
        let left, right = splitAt i l in
        lemma_splitAt l left right i;
        j < length right /\ index right j == index l (j + i))) =
  P.lemma_splitAt_reindex_right i l j
