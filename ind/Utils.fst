(** Core set of utility functions that might be nice to get included
    into ulib *)
module Utils

(** For lists *)
open FStar.List.Tot

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
