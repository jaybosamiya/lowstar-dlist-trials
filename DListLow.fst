module DListLow

open FStar
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Int
open FStar.Ghost
open FStar.Seq
open Gpointers
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module B = FStar.Buffer
module ST = FStar.HyperStack.ST

#set-options "--use_two_phase_tc true"

unopteq
(** Node of a doubly linked list *)
type dlist (t:Type0) = {
  (* forward link *)
  flink: (gpointer_or_null (dlist t));
  (* backward link *)
  blink: (gpointer_or_null (dlist t));
  (* payload *)
  p: t;
}

unopteq
(** Doubly linked list head *)
type dlisthead (t:Type0) ={
  lhead: (gpointer_or_null (dlist t));
  ltail: (gpointer_or_null (dlist t));
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

val getSome: (a:gpointer_or_null 'a{is_not_null a}) -> (b:gpointer 'a{a == b})
let getSome a = a

unfold let (@) (a:gpointer 't) (h0:HS.mem{h0 `B.live` a}) = B.get h0 a 0
unfold let (^@) (a:(gpointer_or_null 't){is_not_null a}) (h0:HS.mem{h0 `B.live` (getSome a)}) = (getSome a) @ h0

unfold let (.[]) (s:seq 'a) (n:nat{n < length s}) = index s n

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let not_aliased (#t:Type) (a:(gpointer_or_null t)) (b:(gpointer_or_null t)) : GTot Type0 =
  is_null a \/ is_null b \/
  disjoint (getSome a) (getSome b)

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let not_aliased0 (#t:Type) (a:gpointer t) (b:(gpointer_or_null t)) : GTot Type0 =
  is_null b \/
  disjoint a (getSome b)

logic
let not_aliased00 (#t:Type) (a:gpointer t) (b:gpointer t) : GTot Type0 =
  disjoint a b

// logic
let dlist_is_valid' (#t:Type) (h0:HS.mem) (n:dlist t) : GTot Type0 =
  not_aliased n.flink n.blink

// logic
let dlist_is_valid (#t:Type) (h0:HS.mem) (n:gpointer (dlist t)) : GTot Type0 =
  h0 `B.live` n /\
  dlist_is_valid' #t h0 (n@h0)

let (==$) (#t:Type) (a:(gpointer_or_null t)) (b:gpointer t) =
  is_not_null a /\
  as_addr (getSome a) = as_addr b

logic
let ( |> ) (#t:Type) (a:dlist t) (b:gpointer (dlist t)) : GTot Type0 =
  a.flink ==$ b

logic
let ( <| ) (#t:Type) (a:gpointer (dlist t)) (b: dlist t) : GTot Type0 =
  b.blink ==$ a

let ( =|> ) (#t:Type) (a:gpointer (dlist t)) (b:gpointer (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `B.live` a /\ h0 `B.live` b /\
         not_aliased00 a b /\
         not_aliased0 b (a@h0).blink))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         b@h1 == b@h2 /\
         (a@h2) |> b)) =
  a := { !a with flink = b }

let ( <|= ) (#t:Type) (a:gpointer (dlist t)) (b:gpointer (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `B.live` a /\ h0 `B.live` b /\
         not_aliased00 a b /\
         not_aliased0 a (b@h0).flink))
    (ensures (fun h1 _ h2 ->
         modifies_1 b h1 h2 /\
         dlist_is_valid h2 b /\
         a@h1 == a@h2 /\
         (b@h1).p == (b@h2).p /\
         (b@h1).flink == (b@h2).flink /\
         a <| (b@h2))) =
  b := { !b with blink = a }

let ( !=|> ) (#t:Type) (a:gpointer (dlist t)) : ST unit
    (requires (fun h0 -> h0 `B.live` a))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         (a@h2).flink == null)) =
  a := { !a with flink = null }

let ( !<|= ) (#t:Type) (a:gpointer (dlist t)) : ST unit
    (requires (fun h0 -> h0 `B.live` a))
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

logic
let all_nodes_contained (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  (is_not_null h.lhead ==> h0 `B.live` (getSome h.lhead)) /\
  (is_not_null h.ltail ==> h0 `B.live` (getSome h.ltail)) /\
  (forall i. {:pattern (h0 `B.live` nodes.[i])}
     h0 `B.live` nodes.[i])

logic
let flink_valid (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern ((nodes.[i]@h0).flink)}
     ((0 <= i /\ i < len - 1) ==>
      (nodes.[i]@h0 |> nodes.[i+1])))

logic
let blink_valid (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern ((nodes.[i]@h0).blink)}
     ((1 <= i /\ i < len) ==>
      (nodes.[i-1] <| nodes.[i]@h0)))

logic
let dlisthead_ghostly_connections (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  all_nodes_contained h0 h /\
  ~empty ==> (
    h.lhead ==$ nodes.[0] /\
    h.ltail ==$ nodes.[len-1] /\
    is_null (h.lhead^@h0).blink /\
    is_null (h.ltail^@h0).flink)

logic
let elements_dont_alias1 (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink)}
     0 < i /\ i < j /\ j < length nodes ==>
   (not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink))

logic
let elements_dont_alias2 (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink)}
     0 < i /\ i < j /\ j < length nodes ==>
   (not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink))

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let elements_dont_alias (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  elements_dont_alias1 h0 h /\
  elements_dont_alias2 h0 h

logic
let elements_are_valid (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern (nodes.[i])}
     dlist_is_valid h0 nodes.[i])

logic
let all_elements_distinct (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
    let nodes = reveal h.nodes in
    (forall i j. {:pattern (nodes.[i]); (nodes.[j])}
       (0 <= i /\ i < j /\ j < Seq.length nodes) ==>
       (disjoint nodes.[i] nodes.[j]))

logic
let dlisthead_is_valid (#t:Type) (h0:HS.mem) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  (empty ==> is_null h.lhead /\ is_null h.ltail) /\
  (~empty ==> dlisthead_ghostly_connections h0 h /\
              flink_valid h0 h /\
              blink_valid h0 h) /\
  elements_are_valid h0 h /\
  elements_dont_alias h0 h /\
  all_elements_distinct h0 h

let test1 () : Tot unit = assert (forall h0 t. dlisthead_is_valid h0 (empty_list #t))

val singletonlist: #t:eqtype -> e:gpointer (dlist t) ->
  ST (dlisthead t)
  (requires (fun h0 -> h0 `B.live` e))
  (ensures (fun h0 y h1 -> modifies_1 e h0 h1 /\ dlisthead_is_valid h1 y))
let singletonlist #t e =
  !<|= e; !=|> e;
  { lhead = e ; ltail = e ; nodes = ~. e }

// logic
let contains_by_addr (#t:Type) (s:seq (gpointer t)) (x:gpointer t) : GTot Type0 =
  (exists i. B.as_addr s.[i] == B.as_addr x)

logic
let member_of (#t:eqtype) (h0:HS.mem) (h:dlisthead t) (e:gpointer (dlist t)) : GTot Type0 =
  let nodes = reveal h.nodes in
  nodes `contains_by_addr` e

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let has_nothing_in (#t:eqtype) (h0:HS.mem)
    (h:dlisthead t{dlisthead_is_valid h0 h})
    (e:gpointer (dlist t){h0 `B.live` e})
  : GTot Type0 =
  (~(member_of h0 h e)) /\
  (not_aliased0 e h.lhead) /\
  (not_aliased0 e h.ltail) /\
  (let nodes = reveal h.nodes in
   (forall i. {:pattern (nodes.[i]@h0).flink}
      (not_aliased0 e (nodes.[i]@h0).flink /\
       not_aliased (e@h0).flink (nodes.[i]@h0).flink /\
       not_aliased (e@h0).blink (nodes.[i]@h0).flink)) /\
   (forall i. {:pattern (nodes.[i]@h0).blink}
      (not_aliased0 e (nodes.[i]@h0).blink) /\
      not_aliased (e@h0).flink (nodes.[i]@h0).blink /\
      not_aliased (e@h0).blink (nodes.[i]@h0).blink))

type nonempty_dlisthead t = (h:dlisthead t{is_not_null h.lhead /\ is_not_null h.ltail})

let is_singleton (#t:Type) (h:nonempty_dlisthead t) : Tot bool =
  compare_addrs (getSome h.lhead) (getSome h.ltail)

val nonempty_singleton_properties :
  #t:Type ->
  h:nonempty_dlisthead t ->
  ST unit
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ is_singleton h))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ Seq.length (reveal h.nodes) == 1))
let nonempty_singleton_properties #t h = ()

val nonempty_nonsingleton_properties :
  #t:Type ->
  h:nonempty_dlisthead t ->
  ST unit
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ ~(compare_addrs (getSome h.lhead) (getSome h.ltail))))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ Seq.length (reveal h.nodes) > 1))
let nonempty_nonsingleton_properties #t h = ()

val ghost_append_properties: #t:Type -> a:t -> b:erased (seq t) ->
  Lemma (let r = a ^+ b in
         forall i j. {:pattern ((reveal b).[i] == (reveal r).[j])}
           j = i + 1 /\ 0 <= i /\ i < length (reveal b) ==> (reveal b).[i] == (reveal r).[j])
let ghost_append_properties #t a b = ()

#set-options "--z3rlimit 50 --z3refresh"

val dlisthead_update_head: #t:eqtype -> h:nonempty_dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies_2 e (getSome h.lhead) h1 h2
                             /\ dlisthead_is_valid h2 y))
let dlisthead_update_head (#t:eqtype) (h:nonempty_dlisthead t) (e:gpointer (dlist t)) =
  let h1 = ST.get () in
  let n = h.lhead in
  !<|= e;
  e =|> n;
  e <|= n;
  let y = { lhead = e ; ltail = h.ltail ; nodes = e ^+ h.nodes } in
  let h2 = ST.get () in
  assert (
    let ynodes = reveal y.nodes in
    let hnodes = reveal h.nodes in
    (forall (i:nat{2 <= i /\ i < Seq.length ynodes /\ i-1 < Seq.length hnodes}).
              {:pattern (ynodes.[i]@h2)}
       ynodes.[i]@h2 == hnodes.[i-1]@h1)); // OBSERVE
  admit ();
    y

#reset-options

val insertHeadList : #t:eqtype -> h:dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 ->
         (is_not_null h.lhead ==>
          modifies_2 e (getSome h.lhead) h1 h2) /\
         (~(is_not_null h.lhead) ==>
          modifies_1 e h1 h2) /\
         dlisthead_is_valid h2 y))
let insertHeadList #t h e =
  if is_not_null h.lhead
  then dlisthead_update_head h e
  else singletonlist e

#set-options "--z3rlimit 25 --z3refresh"

val dlisthead_update_tail: #t:eqtype -> h:nonempty_dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies_2 e (getSome h.ltail) h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_update_tail #t h e =
  let h1 = ST.get () in
  let previously_singleton = is_singleton h in
  let n = h.ltail in
  !=|> e;
  n =|> e;
  n <|= e;
  let y = { lhead = h.lhead ; ltail = e ; nodes = h.nodes +^ e } in
  let h2 = ST.get () in
  assert (
    let ynodes = reveal y.nodes in
    let hnodes = reveal h.nodes in
    (forall (i:nat{0 <= i /\ i < Seq.length ynodes - 2 /\ i < Seq.length hnodes - 1}).
              {:pattern (ynodes.[i]@h2)}
       ynodes.[i]@h2 == hnodes.[i]@h1)); // OBSERVE
  admit ();
    y

#reset-options

val insertTailList : #t:eqtype -> h:dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 ->
         (is_not_null h.ltail ==>
          modifies_2 e (getSome h.ltail) h1 h2) /\
         (~(is_not_null h.lhead) ==>
          modifies_1 e h1 h2) /\
         dlisthead_is_valid h2 y))
let insertTailList #t h e =
  if is_not_null h.ltail
  then dlisthead_update_tail h e
  else singletonlist e

unfold let ghost_tail (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 0}) : Tot (erased (seq t)) =
  hide (Seq.tail (reveal s))

#set-options "--z3rlimit 50 --max_fuel 4 --max_ifuel 1"

val dlisthead_remove_head: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h))
    (ensures (fun h1 y h2 ->
         (is_singleton h ==>
          modifies_1 (getSome h.lhead) h1 h2) /\
         (~(is_singleton h) ==>
          modifies_2 (getSome h.lhead) (reveal h.nodes).[1] h1 h2) /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_head #t h =
  let h1 = ST.get () in
  let n = h.lhead in
  if is_singleton h
  then (
    empty_list
  ) else (
    let next = (!n).flink in
    recall next;
    // unlink them
    !=|> n;
    !<|= next;
    let htail = h.ltail in
    let y = { lhead = next ; ltail = h.ltail ; nodes = ghost_tail h.nodes } in
    let h2 = ST.get () in
    assert (
      let ynodes = reveal y.nodes in
      let hnodes = reveal h.nodes in
      (forall (i:nat{1 <= i /\ i < Seq.length ynodes /\ i+1 < Seq.length hnodes}).
                {:pattern (ynodes.[i]@h2)}
         ynodes.[i]@h2 == hnodes.[i+1]@h1)); // OBSERVE
    admit ();
      y
  )

#reset-options

unfold let ghost_unsnoc (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 0}) : Tot (erased (seq t)) =
  let x = reveal s in
  let l = length x - 1 in
  hide (slice x 0 l)

#set-options "--z3rlimit 50"

val dlisthead_remove_tail: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h))
    (ensures (fun h1 y h2 ->
         (is_singleton h ==>
          modifies_1 (getSome h.ltail) h1 h2) /\
         (~(is_singleton h) ==>
          (let nodes = reveal h.nodes in
          modifies_2 (getSome h.ltail) nodes.[length nodes - 2] h1 h2)) /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_tail #t h =
  let h1 = ST.get () in
  if is_singleton h then (
    empty_list
  ) else (
    let n = h.ltail in
    let prev = (!n).blink in
    recall prev;
    //unlink them
    !<|= n;
    !=|> prev;
    let y = { lhead = h.lhead ; ltail = prev ; nodes = ghost_unsnoc h.nodes } in
    let h2 = ST.get () in
    assert (
      let ynodes = reveal y.nodes in
      let hnodes = reveal h.nodes in
      (forall (i:nat{0 <= i /\ i < Seq.length ynodes - 1 /\ i < Seq.length hnodes - 2}).
                {:pattern (ynodes.[i]@h2)}
         ynodes.[i]@h2 == hnodes.[i]@h1)); // OBSERVE
    admit ();
      y
  )

#reset-options

let rec get_ref_index (#t:Type) (s:seq (gpointer t)) (x:gpointer t{s `contains_by_addr` x}) :
  GTot (i:nat{i < Seq.length s})
    (decreases (Seq.length s)) =
  contains_elim s x;
  let h, t = Seq.head s, Seq.tail s in
  if compare_addrs h x then 0 else (
    contains_cons h t x;
    1 + get_ref_index t x)

val lemma_get_ref_index : #t:Type -> s:seq (gpointer t) -> x:gpointer t{s `contains_by_addr` x} ->
  Lemma (ensures (
    compare_addrs s.[get_ref_index s x] x))
    (decreases (Seq.length s))
    [SMTPat (s.[get_ref_index s x])]
let rec lemma_get_ref_index #t s x =
  contains_elim s x;
  let h, t = Seq.head s, Seq.tail s in
  if compare_addrs h x then () else (
    contains_cons h t x;
    lemma_get_ref_index t x)

val split_seq_at_element : #t:Type -> s:seq (gpointer t) -> x:gpointer t{s `contains_by_addr` x} ->
  GTot (v:(seq (gpointer t) * nat * seq (gpointer t)){
      let l, i, r = v in
      indexable s i /\ (
      s == append l (cons s.[i] r) /\
      compare_addrs s.[i] x)
  })
let split_seq_at_element #t s x =
  let i = get_ref_index s x in
  let l, mr = Seq.split s i in
  lemma_split s i;
  l, i, tail mr

#reset-options "--z3rlimit 1 --detail_errors --z3rlimit_factor 20"

val dlisthead_remove_strictly_mid: #t:eqtype -> h:nonempty_dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\
                         member_of h0 h e /\
                         not_aliased0 e h.lhead /\ not_aliased0 e h.ltail))
    (ensures (fun h1 y h2 ->
         is_not_null (e@h1).flink /\ is_not_null (e@h1).blink /\
         dlist_is_valid h2 e /\
         is_null (e@h2).flink /\ is_null (e@h2).blink /\
         modifies_3 e (getSome (e@h1).flink) (getSome (e@h1).blink) h1 h2 /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_strictly_mid #t h e =
  let h1 = ST.get () in
  let prev = (!e).blink in
  let next = (!e).flink in
  recall prev;
  recall next;
  !<|= e;
  !=|> e;
  admit ();
  prev =|> next;
  prev <|= next;
  let nodes = h.nodes in // TODO: Fix this
  let y = { lhead = h.lhead ; ltail = h.ltail ; nodes = nodes } in
  admit ();
  h // TODO: Actually do something

/// Useful code that can be copied over below

(*
    assert (all_nodes_contained h2 y);
    assert (dlisthead_ghostly_connections h2 y);
    assert (flink_valid h2 y);
    assert (blink_valid h2 y);
    assert (elements_are_valid h2 y);
    assert (elements_dont_alias1 h2 y);
    assert (elements_dont_alias2 h2 y);
    assert (all_elements_distinct h2 y);
*)
