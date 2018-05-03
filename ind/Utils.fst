(** Core set of utility functions that might be nice to get included
    into ulib *)
module Utils

(** For lists *)
open FStar.List.Tot

let snoc (#t:Type) (a:list t) (b:t) : (c:list t{length c = length a + 1}) =
  append_length a [b];
  append a [b]

let rec lemma_splitAt (#t:Type) (n:nat) (l:list t) :
  Lemma (requires n < length l)
    (ensures (let a, b = splitAt n l in
              length a = n /\ length b = length l - n /\ append a b == l)) =
  match n with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> ()
    | x :: xs -> lemma_splitAt (n-1) xs

let unsnoc (#t:Type) (l:list t{length l <> 0}) : (r:(list t * t){l == snoc (fst r) (snd r)}) =
  let l', a = splitAt (length l - 1) l in
  lemma_splitAt (length l - 1) l;
  assert (length a > 0);
  l', hd a

let split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  r:(list t * t * list t){
    let a, b, c = r in
    (l == append a (b :: c)) /\
    (length a = i) /\ (length c = (length l - i) - 1)} =
  let a, as = splitAt i l in
  lemma_splitAt i l;
  let b :: c = as in
  a, b, c

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
