module DList

open FStar
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Int
open C
open C.Nullity
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Seq = FStar.Seq
module Ghost = FStar.Ghost
module ST = FStar.HyperStack.ST

open PointerEquality

(** Type of a network buffer *)
type buffer_t = Buffer.buffer(UInt8.t)

unopteq
(** A doubly-linked list of a type*)
type dlist (t:Type0) = {
(* Forward link *)
  flink: pointer_or_null (dlist t);
(* Backward link *)
  blink: pointer_or_null (dlist t);
(* payload *)
  p: t;
}

unopteq
(** Head of a doubly linked list *)
type dlisthead (t:Type) = {
  (* head forward link *)
  lhead: pointer_or_null (dlist t);
  (* head backward link *)
  ltail: pointer_or_null (dlist t);
  (* all nodes in this dlist *)
  nodes: erased (seq (dlist t))
}

(** Be able to use [null] very very easily *)
inline_for_extraction private unfold
let null #t = null t

(** Initialze an element of a doubly linked list *)
let empty_entry (#t:Type) (payload:t): dlist(t) =
  { flink = null; blink = null; p = payload; }

(** Initialize a doubly-linked list head *)
let empty_list (#t:Type) : dlisthead t =
  { lhead = null; ltail = null; nodes = hide createEmpty}

unfold let op_At_Bang (#t:Type) (h0:mem) (p:pointer t) = Buffer.get h0 p 0
unfold let op_String_Access = Seq.index
unfold let not_null (#t:Type) (a:pointer_or_null t) = Buffer.length a <> 0

let _ = assert_norm (forall (t:Type) (p:pointer_or_null t). is_null p \/ not_null p)

unfold
let dlisthead_is_valid (#t:Type) (h0:mem) (h:dlisthead t) =
  let nodes = Ghost.reveal h.nodes in
  let l = Seq.length nodes in
  let empty = l = 0 in
  (empty <==> is_null h.ltail) /\
  (empty <==> is_null h.lhead) /\
  (~empty ==> (is_null (h0@! h.lhead).blink) /\
              (is_null (h0@! h.ltail).flink) /\
              (live h0 h.lhead /\ live h0 h.ltail) /\
              (h0@! h.ltail == nodes.[l-1]) /\
              (h0@! h.lhead == nodes.[0]) /\
              (forall i. {:pattern (nodes.[i]).blink}
                 ((1 <= i /\ i < l) ==>
                  not_null (nodes.[i]).blink /\
                  h0@! (nodes.[i]).blink == nodes.[i-1])) /\
              (forall i. {:pattern (nodes.[i]).flink}
                 ((0 <= i /\ i < l - 1) ==>
                  not_null (nodes.[i]).flink /\
                  h0@! (nodes.[i]).flink == nodes.[i+1])))

let _ = assert_norm (forall t. forall h0. dlisthead_is_valid #t h0 empty_list)

unfold
let dlist_is_member_of (#t:eqtype) (h0:mem) (e:pointer (dlist t)) (h:dlisthead t) =
  Seq.mem (h0@! e) (Ghost.reveal h.nodes)

unfold inline_for_extraction
let (<&) (#t:Type) (p:pointer t) (x:t) =
  p.(0ul) <- x

let erased_single_node (#t:eqtype) (e:pointer (dlist t)) =
  hide (Seq.create 1 !*e)

// #set-options "--z3rlimit 1" // Forces it to quickly hit resource bounds and then --detail_errors seems to get it through ¯\_(ツ)_/¯

#set-options "--max_fuel 64 --max_ifuel 64 --z3rlimit 10"

let createSingletonList (#t:eqtype) (e:pointer (dlist t)): ST (dlisthead t)
    (requires (fun h0 -> live h0 e))
    (ensures (fun h1 y h2 -> modifies_1 e h1 h2 /\ live h2 e /\ dlisthead_is_valid h2 y)) =
  let h1 = ST.get () in
  e <& { !*e with flink=null; blink = null }; // isn't this inefficient?
  let y = { lhead = e; ltail = e; nodes = erased_single_node e } in
  let h2 = ST.get () in
  assert (is_null (h2@! e).flink /\
          is_null (h2@! e).blink);
  assert (y.lhead == e /\ y.ltail == e);
  assert (Seq.length (Ghost.reveal y.nodes) == 1);
  assert (live h2 e);
  assert (live h2 y.lhead /\ live h2 y.ltail);
  assert (h2@! y.lhead == (Ghost.reveal y.nodes).[0]);
  assert (h2@! y.ltail == (Ghost.reveal y.nodes).[0]);
  assert ((forall i. {:pattern ((Ghost.reveal y.nodes).[i]).blink}
             ((1 <= i /\ i < 1) ==>
              not_null ((Ghost.reveal y.nodes).[i]).blink /\
              h2@! ((Ghost.reveal y.nodes).[i]).blink == (Ghost.reveal y.nodes).[i-1])) );
  assert ((forall i. {:pattern ((Ghost.reveal y.nodes).[i]).flink}
             ((0 <= i /\ i < 0) ==>
              not_null ((Ghost.reveal y.nodes).[i]).flink /\
              h2@! ((Ghost.reveal y.nodes).[i]).flink == (Ghost.reveal y.nodes).[i+1])));
  assert (dlisthead_is_valid h2 y);
  assert (live h2 e);
  assert (modifies_1 e h1 h2);
  assert (modifies_1 e h1 h2 /\ live h2 e /\ dlisthead_is_valid h2 y);
  y


(** Insert an element e as the first element in a doubly linked list *)
let insertHeadList (#t:eqtype) (h:dlisthead t) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun h0 -> dlisthead_is_valid h0 h /\ live h0 e /\ ~(dlist_is_member_of h0 e h)))
   (ensures (fun _ y h2 -> live h2 e /\ dlisthead_is_valid h2 y))
=
  if is_null h.lhead then ( // the list is empty
    createSingletonList e
  ) else (
    let next = h.lhead in
    admit ();
    next <& { !*next with blink = e; };
    e <& { !*e with flink = next; blink = null };
    let ghoste = hide !*e in
    let y = { lhead = e; ltail = h.ltail; nodes = elift2 Seq.cons ghoste h.nodes } in
    let h2 = ST.get () in assert ( dlisthead_is_valid h2 y );
    admit ();
    y
  )
