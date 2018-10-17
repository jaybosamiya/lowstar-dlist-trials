(** Core set of utility functions that might be nice to get included
    into ulib *)
module Utils

(** For lists *)
module T = FStar.List.Tot
module P =  FStar.List.Pure
open T
open P

let snoc (#t:Type) (a:list t) (b:t) : (c:list t) =
  T.snoc (a, b)

let lemma_snoc_length (#t:Type) (a:list t) (b:t) :
  Lemma (length (snoc a b) = length a + 1)
    [SMTPat (length (snoc a b))] =
  T.lemma_snoc_length (a, b)

let rec lemma_splitAt (#t:Type) (n:nat) (l:list t) :
  Lemma (requires n <= length l)
    (ensures (let a, b = splitAt n l in
              length a = n /\ length b = length l - n /\ append a b == l)) =
  let a, b = splitAt n l in
  P.lemma_splitAt l a b n

let rec lemma_index_splitAt (#t:Type) (i:nat) (l:list t) :
  Lemma
    (requires (i < length l))
    (ensures (let a, b = splitAt i l in
              lemma_splitAt i l;
              length b > 0 /\ hd b == index l i)) =
  lemma_splitAt_index_hd i l

let unsnoc (#t:Type) (l:list t{length l <> 0}) : (r:(list t * t){l == snoc (fst r) (snd r)}) =
  T.unsnoc l

let split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  r:(list t * t * list t){
    let a, b, c = r in
    (l == append a (b :: c)) /\
    (b == index l i) /\
    (length a = i) /\ (length c = (length l - i) - 1)} =
  P.lemma_split3_append l i;
  P.lemma_split3_index l i;
  P.lemma_split3_length l i;
  T.split3 l i

let lemma_split3_leftprefix (#t:Type) (l1:list t) (l2:list t) (i:nat{i < length l1 /\ i < length l2}) :
  Lemma
    (requires (fst (splitAt (i+1) l1) == fst (splitAt (i+1) l2)))
    (ensures (
        let a1, b1, c1 = split3 l1 i in
        let a2, b2, c2 = split3 l2 i in
        a1 == a2 /\ b1 == b2)) =
  P.lemma_split3_on_same_leftprefix l1 l2 i

let rec lemma_unsnoc_split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (requires (i <> length l - 1))
    (ensures (
        let a, b, c = split3 l i in
        let xs, x = unsnoc l in
        let ys, y = unsnoc c in
        append a (b :: ys) == xs)) =
  P.lemma_split3_unsnoc l i

let rec lemma_splitAt_shorten_left
    (#t:Type) (l1 l2:list t) (i:nat{i <= length l1 /\ i <= length l2}) (j:nat{j <= i}) :
  Lemma
    (requires (fst (splitAt i l1) == fst (splitAt i l2)))
    (ensures (fst (splitAt j l1) == fst (splitAt j l2))) =
  P.lemma_splitAt_shorten_left l1 l2 i j

let rec lemma_split3_unsnoc (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (requires (i <> length l - 1))
    (ensures (
        let xs, x = unsnoc l in
        let a0, b0, c0 = split3 l i in
        let a1, b1, c1 = split3 xs i in
        a0 == a1 /\ b0 == b1)) =
  P.lemma_unsnoc_split3 l i

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
    (ensures (index (fst (unsnoc l)) i == index l i)) =
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
              length c > 0 ==> hd c == index l (i + 1))) =
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
        lemma_splitAt i l;
        j < length left /\ index left j == index l j)) =
  P.lemma_splitAt_reindex_left i l j

let rec lemma_splitAt_reindex_right (#t:Type) (i:nat) (l:list t) (j:nat) :
  Lemma
    (requires i <= length l /\ j + i < length l)
    (ensures (
        let left, right = splitAt i l in
        lemma_splitAt i l;
        j < length right /\ index right j == index l (j + i))) =
  P.lemma_splitAt_reindex_right i l j
