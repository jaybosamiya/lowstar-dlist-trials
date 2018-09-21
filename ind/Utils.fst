(** Core set of utility functions that might be nice to get included
    into ulib *)
module Utils

(** For lists *)
open FStar.List.Tot
open FStar.List.Pure

let snoc (#t:Type) (a:list t) (b:t) : (c:list t{length c = length a + 1}) =
  append_length a [b];
  append a [b]

let rec lemma_splitAt (#t:Type) (n:nat) (l:list t) :
  Lemma (requires n <= length l)
    (ensures (let a, b = splitAt n l in
              length a = n /\ length b = length l - n /\ append a b == l)) =
  match n with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> ()
    | x :: xs -> lemma_splitAt (n-1) xs

let rec lemma_index_splitAt (#t:Type) (i:nat) (l:list t) :
  Lemma
    (requires (i < length l))
    (ensures (let a, b = splitAt i l in
              lemma_splitAt i l;
              hd b == index l i)) =
  let x :: xs = l in
  if i = 0 then () else lemma_index_splitAt (i - 1) (tl l)

let unsnoc (#t:Type) (l:list t{length l <> 0}) : (r:(list t * t){l == snoc (fst r) (snd r)}) =
  let l', a = splitAt (length l - 1) l in
  lemma_splitAt (length l - 1) l;
  assert (length a > 0);
  l', hd a

let split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  r:(list t * t * list t){
    let a, b, c = r in
    (l == append a (b :: c)) /\
    (b == index l i) /\
    (length a = i) /\ (length c = (length l - i) - 1)} =
  let a, as = splitAt i l in
  lemma_splitAt i l;
  lemma_index_splitAt i l;
  let b :: c = as in
  a, b, c

let lemma_split3_leftprefix (#t:Type) (l1:list t) (l2:list t) (i:nat{i < length l1 /\ i < length l2}) :
  Lemma
    (requires (fst (splitAt (i+1) l1) == fst (splitAt (i+1) l2)))
    (ensures (
        let a1, b1, c1 = split3 l1 i in
        let a2, b2, c2 = split3 l2 i in
        a1 == a2 /\ b1 == b2)) =
  let a1, b1, c1 = split3 l1 i in
  let a2, b2, c2 = split3 l2 i in
  append_l_cons b1 c1 a1;
  append_l_cons b2 c2 a2;
  // assert ((a1 @ [b1]) @ c1 == l1);
  // assert ((a2 @ [b2]) @ c2 == l2);
  let x1, y1 = splitAt (i+1) l1 in
  let x2, y2 = splitAt (i+1) l2 in
  lemma_splitAt (i+1) l1;
  lemma_splitAt (i+1) l2;
  // assert (x1 @ y1 == (a1 @ [b1]) @ c1);
  // assert (x2 @ y2 == (a2 @ [b2]) @ c2);
  append_length_inv_head x1 y1 (append a1 [b1]) c1;
  append_length_inv_head x2 y2 (append a2 [b2]) c2;
  // assert (a1 @ [b1] == a2 @ [b2]);
  append_length_inv_tail a1 [b1] a2 [b2];
  // assert (a1 == a2 /\ b1 == b2);
  ()

let rec lemma_unsnoc_split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (requires (i <> length l - 1))
    (ensures (
        let a, b, c = split3 l i in
        let xs, x = unsnoc l in
        let ys, y = unsnoc c in
        append a (b :: ys) == xs)) =
  match i with
  | 0 -> ()
  | _ -> lemma_unsnoc_split3 (tl l) (i-1)

let rec lemma_splitAt_shorten_left
    (#t:Type) (l1 l2:list t) (i:nat{i <= length l1 /\ i <= length l2}) (j:nat{j <= i}) :
  Lemma
    (requires (fst (splitAt i l1) == fst (splitAt i l2)))
    (ensures (fst (splitAt j l1) == fst (splitAt j l2))) =
  match j with
  | 0 -> ()
  | _ ->
    lemma_splitAt_shorten_left (tl l1) (tl l2) (i-1) (j-1)

let rec lemma_split3_unsnoc (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (requires (i <> length l - 1))
    (ensures (
        let xs, x = unsnoc l in
        let a0, b0, c0 = split3 l i in
        let a1, b1, c1 = split3 xs i in
        a0 == a1 /\ b0 == b1)) =
  let xs, x = unsnoc l in
  let a0, b0, c0 = split3 l i in
  let a1, b1, c1 = split3 xs i in
  splitAt_length_total xs;
  // assert (fst (splitAt (length xs) xs) == xs);
  // assert (fst (splitAt (length xs) xs) == fst (splitAt (length xs) l));
  // assert (i+1 <= length xs);
  lemma_splitAt_shorten_left xs l (length xs) (i+1);
  // assert (fst (splitAt (i+1) xs) == fst (splitAt (i+1) l));
  lemma_split3_leftprefix l xs i

let rec lemma_last_append (#t:Type) (l1 l2:list t) :
  Lemma
    (requires (length l2 > 0))
    (ensures (last (l1 @ l2) == last l2)) =
  match l1 with
  | [] -> ()
  | _ :: l1' -> lemma_last_append l1' l2

let rec lemma_unsnoc_append (#t:Type) (l1 l2:list t) :
  Lemma
    (requires (length l2 > 0)) // the [length l2 = 0] is trivial
    (ensures (
        let as, a = unsnoc (l1 @ l2) in
        let bs, b = unsnoc l2 in
        as == l1 @ bs /\ a == b)) =
  match l1 with
  | [] -> ()
  | _ :: l1' -> lemma_unsnoc_append l1' l2

let rec unsnoc_is_last (#t:Type) (l:list t) :
  Lemma
    (requires (length l > 0))
    (ensures (snd (unsnoc l) == last l /\ snd (unsnoc l) == index l (length l - 1))) =
  match l with
  | [_] -> ()
  | _ -> unsnoc_is_last (tl l)

let rec split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (list t * list t) =
  match l with
  | [_] -> [], l
  | a :: as ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x) then (
      [], l
    ) else (
      let l1', l2' = split_using as x in
      a :: l1', l2'
    )

let rec lemma_split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  Lemma
    (ensures (
        let l1, l2 = split_using l x in
        (length l2 > 0) /\
        ~(x `memP` l1) /\ (hd l2 == x) /\
        append l1 l2 == l)) =
  match l with
  | [_] -> ()
  | a :: as ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x)
    then ()
    else lemma_split_using (tl l) x

let rec index_fst_unsnoc (#t:Type) (l:list t) (i:nat) :
  Lemma
    (requires (length l > 0 /\ i < length l - 1))
    (ensures (index (fst (unsnoc l)) i == index l i)) =
  match i with
  | 0 -> ()
  | _ -> index_fst_unsnoc (tl l) (i - 1)

let rec lemma_splitAt_append (#t:Type) (l1 l2:list t) :
  Lemma
    (ensures (splitAt (length l1) (append l1 l2) == (l1, l2))) =
  match l1 with
  | [] -> ()
  | _ -> lemma_splitAt_append (tl l1) l2

let rec index_of (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (i:nat{i < length l /\ index l i == x}) =
  match l with
  | [_] -> 0
  | a :: as ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x) then (
      0
    ) else (
      1 + index_of as x
    )

let rec lemma_hd_r_split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (let a, b, c = split3 l i in
              length c > 0 ==> hd c == index l (i + 1))) =
  match i with
  | 0 -> ()
  | _ -> lemma_hd_r_split3 (tl l) (i - 1)

let rec indexed_implies_memP (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (index l i `memP` l))
    [SMTPat (index l i `memP` l)] =
  match i with
  | 0 -> ()
  | _ -> indexed_implies_memP (tl l) (i - 1)

let rec lemma_splitAt_reindex_left (#t:Type) (i:nat) (l:list t) (j:nat) :
  Lemma
    (requires i <= length l /\ j < i)
    (ensures (
        let left, right = splitAt i l in
        lemma_splitAt i l;
        index left j == index l j)) =
  match i, j with
  | 1, _ | _, 0 -> ()
  | _ -> lemma_splitAt_reindex_left (i - 1) (tl l) (j - 1)

let rec lemma_splitAt_reindex_right (#t:Type) (i:nat) (l:list t) (j:nat) :
  Lemma
    (requires i <= length l /\ j + i < length l)
    (ensures (
        let left, right = splitAt i l in
        lemma_splitAt i l;
        index right j == index l (j + i))) =
  match i with
  | 0 -> ()
  | _ -> lemma_splitAt_reindex_right (i - 1) (tl l) j
