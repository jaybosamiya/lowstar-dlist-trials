module DListRefInd

open FStar
open FStar.Ghost
open FStar.Seq
open FStar.Ref
open GpointersViaRefs

#set-options "--use_two_phase_tc true --__no_positivity"

unopteq
(** Node of a doubly linked list *)
type dlist (t:Type0) = {
  (* forward link *)
  flink: gpointer_or_null (dlist t);
  (* backward link *)
  blink: gpointer_or_null (dlist t);
  (* payload *)
  p: t;
}

unopteq
(** Doubly linked list head *)
type dlisthead (t:Type0) ={
  lhead: gpointer_or_null (dlist t);
  ltail: gpointer_or_null (dlist t);
  nodes: erased (seq (gpointer (dlist t)));
}

(** Initialize an element of a doubly linked list *)
val empty_entry: #t:Type -> payload:t -> dlist t
let empty_entry #t payload =
  { flink = null ; blink = null ; p = payload }

(** Initialize a doubly linked list head *)
val empty_list: #t:Type -> dlisthead t
let empty_list #t =
  { lhead = null ; ltail = null ; nodes = hide createEmpty }

unfold let (.[]) (s:seq 'a) (n:nat{n < length s}) = index s n

logic
let dlist_is_valid' (#t:Type) (h0:heap) (n:dlist t) : GTot Type0 =
  not_aliased n.flink n.blink

// logic
let dlist_is_valid (#t:Type) (h0:heap) (n:gpointer (dlist t)) : GTot Type0 =
  h0 `contains` n /\
  dlist_is_valid' h0 (n@h0)

logic
let ( |> ) (#t:Type) (a:dlist t) (b:gpointer (dlist t)) : GTot Type0 =
  a.flink ==$ b

logic
let ( <| ) (#t:Type) (a:gpointer (dlist t)) (b: dlist t) : GTot Type0 =
  b.blink ==$ a

irreducible
let ( =|> ) (#t:Type) (a:gpointer (dlist t)) (b:gpointer (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 b (a@h0).blink))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         b@h1 == b@h2 /\
         (a@h2) |> b)) =
  a := { !a with flink = of_non_null b }

irreducible
let ( <|= ) (#t:Type) (a:gpointer (dlist t)) (b:gpointer (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 a (b@h0).flink))
    (ensures (fun h1 _ h2 ->
         modifies_1 b h1 h2 /\
         dlist_is_valid h2 b /\
         a@h1 == a@h2 /\
         (b@h1).p == (b@h2).p /\
         (b@h1).flink == (b@h2).flink /\
         a <| (b@h2))) =
  b := { !b with blink = of_non_null a }

irreducible
let ( !=|> ) (#t:Type) (a:gpointer (dlist t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         (a@h2).flink == null)) =
  a := { !a with flink = null }

irreducible
let ( !<|= ) (#t:Type) (a:gpointer (dlist t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).flink == (a@h2).flink /\
         (a@h2).blink == null)) =
  a := { !a with blink = null }

unfold let (~.) (#t:Type) (a:t) : Tot (erased (seq t)) = hide (Seq.create 1 a)
unfold let (^+) (#t:Type) (a:t) (b:erased (seq t)) : Tot (erased (seq t)) = elift2 Seq.cons (hide a) b
unfold let (+^) (#t:Type) (a:erased (seq t)) (b:t) : Tot (erased (seq t)) = elift2 Seq.snoc a (hide b)

(** Some convenience type definitions *)
type nodeptr t = gpointer (dlist t)
type nodeseq t = (s:seq (nodeptr t))

let rec all_nodes_contained_aux (#t:Type) (h0:heap) (s:nodeseq t) :
  GTot Type0 (decreases (Seq.length s)) =
  (if Seq.length s = 0 then True else
     h0 `contains` (Seq.head s) /\
     all_nodes_contained_aux h0 (Seq.tail s))

let all_nodes_contained (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  all_nodes_contained_aux h0 (reveal h.nodes)

let rec node_contained (#t:Type) (h0:heap) (s:nodeseq t) (idx:nat{idx < length s}) :
  Lemma
    (requires all_nodes_contained_aux h0 s)
    (ensures h0 `contains` s.[idx])
    (decreases %[length s])
  =
  match idx with
  | 0 -> ()
  | _ ->
    node_contained h0 (Seq.tail s) (idx - 1)

let rec flink_valid_aux (#t:Type) (h0:heap) (s:nodeseq t)
  : GTot Type0 (decreases (Seq.length s)) =
  all_nodes_contained_aux h0 s /\
  (if Seq.length s <= 1 then True else
     s.[0]@h0 |> s.[1] /\
     flink_valid_aux h0 (Seq.tail s))

let flink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  flink_valid_aux h0 (reveal h.nodes)

let rec blink_valid_aux (#t:Type) (h0:heap) (s:nodeseq t)
  : GTot Type0 (decreases (Seq.length s)) =
  all_nodes_contained_aux h0 s /\
  (if Seq.length s <= 1 then True else
     s.[0] <| s.[1]@h0 /\
     flink_valid_aux h0 (Seq.tail s))

let blink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  blink_valid_aux h0 (reveal h.nodes)

logic
let dlisthead_ghostly_connections (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  all_nodes_contained h0 h /\
  ~empty ==> (h.lhead ==$ Seq.head nodes /\
             h.ltail ==$ Seq.last nodes)

logic
let dlisthead_nothing_outside (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  all_nodes_contained h0 h /\
  ~empty ==> (is_null ((Seq.head nodes)@h0).blink /\
              (node_contained h0 nodes (len - 1);
               is_null ((Seq.last nodes)@h0).flink))

// logic
let rec elements_dont_alias_flink_aux' (#t:Type) (h0:heap) (s:nodeseq t) (i:nat{0 < i /\ i < length s})
  : GTot Type0 (decreases (length s - i)) =
  all_nodes_contained_aux h0 s /\
  (node_contained h0 s i;
   not_aliased (s.[0]@h0).flink (s.[i]@h0).flink) /\
  (if i + 1 < length s then elements_dont_alias_flink_aux' h0 s (i+1) else True)

logic
let rec elements_dont_alias_flink_aux (#t:Type) (h0:heap) (s:nodeseq t)
  : GTot Type0 (decreases (Seq.length s)) =
  (if Seq.length s <= 1 then True else
     elements_dont_alias_flink_aux' h0 s 1 /\
     elements_dont_alias_flink_aux h0 (Seq.tail s))

// logic
let rec elements_dont_alias_blink_aux' (#t:Type) (h0:heap) (s:nodeseq t) (i:nat{0 < i /\ i < length s})
  : GTot Type0 (decreases (length s - i)) =
  all_nodes_contained_aux h0 s /\
  (node_contained h0 s i;
   not_aliased (s.[0]@h0).blink (s.[i]@h0).blink) /\
  (if i + 1 < length s then elements_dont_alias_blink_aux' h0 s (i+1) else True)

logic
let rec elements_dont_alias_blink_aux (#t:Type) (h0:heap) (s:nodeseq t)
  : GTot Type0 (decreases (Seq.length s)) =
  (if Seq.length s <= 1 then True else
     elements_dont_alias_blink_aux' h0 s 1 /\
     elements_dont_alias_blink_aux h0 (Seq.tail s))

// logic
let elements_dont_alias (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  elements_dont_alias_flink_aux h0 (reveal h.nodes) /\
  elements_dont_alias_blink_aux h0 (reveal h.nodes)

logic
let rec elements_are_valid_aux (#t:Type) (h0:heap) (s:nodeseq t) :
  GTot Type0 (decreases (Seq.length s)) =
  (if Seq.length s = 0 then True else
     dlist_is_valid h0 (Seq.head s) /\
     elements_are_valid_aux h0 (Seq.tail s))

logic
let elements_are_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  elements_are_valid_aux h0 (reveal h.nodes)

#set-options "--detail_errors"

let rec two_elements_distinct (#t:Type) (h0:heap) (h:dlisthead t) (i j:int) : Lemma
  (requires (0 <= i /\ i < j /\ j < Seq.length (reveal h.nodes)) /\
            dlisthead_nothing_outside h0 h /\
            blink_valid h0 h /\
            elements_are_valid h0 h)
  (ensures
     (let nodes = reveal h.nodes in
      disjoint nodes.[i] nodes.[j])) =
  let nodes = reveal h.nodes in
  if 0 <= i && i < j && j < Seq.length nodes then (
    let b = FStar.StrongExcludedMiddle.strong_excluded_middle (disjoint nodes.[i] nodes.[j]) in
    if not b then (
      if i = 0 then (
        assert( is_null (nodes.[i]@h0).blink);
        node_contained h0 nodes j;
        assert( is_not_null (nodes.[j]@h0).blink)
      ) else (
        two_elements_distinct h0 h (i - 1) (j - 1)
      )
    ) else ()
  ) else ()
