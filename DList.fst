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
inline_for_extraction abstract private
let null #t = null t

(** Initialze an element of a doubly linked list *)
let empty_entry (#t:Type) (payload:t): dlist(t) =
  { flink = null; blink = null; p = payload; }

(** Initialize a doubly-linked list head *)
let empty_list (#t:Type) : dlisthead t =
  { lhead = null; ltail = null; nodes = hide createEmpty}

let op_At_Bang (#t:Type) (h0:mem) (p:pointer t) = Buffer.get h0 p 0
let op_String_Access = Seq.index
let not_null a = ~(is_null a)

let dlisthead_is_valid (#t:Type) (h0:mem) (h:dlisthead t) =
  let nodes = Ghost.reveal h.nodes in
  let l = Seq.length nodes in
  let empty = l = 0 in
  (empty <==> is_null h.ltail) /\
  (empty <==> is_null h.lhead) /\
  (~empty ==> (is_null (h0@! h.lhead).blink) /\
              (is_null (h0@! h.ltail).flink) /\
              (h0@! h.ltail == nodes.[l-1]) /\
              (h0@! h.lhead == nodes.[0]) /\
              (forall i. {:pattern (nodes.[i]).blink}
                 ((1 <= i /\ i < Seq.length nodes) ==>
                  not_null (nodes.[i]).blink /\
                  h0@! (nodes.[i]).blink == nodes.[i-1])) /\
              (forall i. {:pattern (nodes.[i]).flink}
                 ((0 <= i /\ i < Seq.length nodes - 1) ==>
                  not_null (nodes.[i]).flink /\
                  h0@! (nodes.[i]).flink == nodes.[i+1])))

let _ = assert_norm (forall t. forall h0. dlisthead_is_valid #t h0 empty_list)

let dlist_is_member_of (#t:eqtype) (h0:mem) (e:pointer (dlist t)) (h:dlisthead t) =
  Seq.mem (h0@! e) (Ghost.reveal h.nodes)

unfold inline_for_extraction
let (<&) (#t:Type) (p:pointer t) (x:t) : ST unit
    (fun h0 -> live h0 p)
    (fun h1 () h2 -> modifies_1 p h1 h2) =
  p.(0ul) <- x

unfold inline_for_extraction
let (<~) (#t:Type) (p:pointer t) (q:pointer t) : ST unit
    (fun h0 -> live h0 p /\ live h0 q)
    (fun h1 () h2 -> modifies_1 p h1 h2)
  = p <& !*q

(** Insert an element e as the first element in a doubly linked list *)
let insertHeadList (#t:eqtype) (h:dlisthead t) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun h0 -> dlisthead_is_valid h0 h /\ live h0 e /\ ~(dlist_is_member_of h0 e h)))
   (ensures (fun _ y h2 -> dlisthead_is_valid h2 y))
=
  if is_null h.lhead then ( // the list is empty
    e.(0ul) <- { e.(0ul) with flink=null; blink = null }; // isn't this inefficient?
    // e <& { !*e with flink=null; blink = null }; // isn't this inefficient?
    assert (not_null e);
    let y = { lhead = e; ltail = e; nodes = hide (Seq.create 1 !*e) } in
    // admit ();
    // let h2 = ST.get () in assert ( dlisthead_is_valid h2 y ); // not sure why F* needs this coaxing
    y
  ) else (
    let next = h.lhead in
    admit ();
    next <& { !*next with blink = e; };
    e <& { !*e with flink = next; blink = null };
    let ghoste = hide !*e in
    let y = { lhead = e; ltail = h.ltail; nodes = elift2 Seq.cons ghoste h.nodes } in
    let h2 = ST.get () in assert ( dlisthead_is_valid h2 y );
    y
  )

(*
(** Insert an element e as the last element in a doubly linked list. *)
let insertTailList (#t:Type) (h:dlisthead t) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun h0 -> dlisthead_is_valid h0 h /\ live h0 e))
   (ensures (fun _ y h2 -> dlisthead_is_valid h2 y))
=
  if is_null h.lhead then ( // the list is empty
    e.(0ul) <- { !*e with flink=null; blink = null };
    { lhead = e; ltail = e; nodes = hide (Seq.create 1 !*e) }
  ) else (
    let prev = h.ltail in
    prev.(0ul) <- { !*prev with flink=e; }; // tail->flink=e
    e.(0ul) <- { !*e with flink=null; blink = prev }; // e->flink=null/e.blink=tail
    let ghoste = hide !*e in
    { lhead = h.lhead; ltail = e; nodes = elift2 Seq.snoc h.nodes ghoste }
  )

(** Remove entry e from the doubly linked list *)
let removeEntryList (#t:eqtype) (h:dlisthead t) (e:pointer (dlist t)): ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ not (is_null h.lhead) /\ live h0 e /\
         (h.lhead == e <==> is_null ((get h0 e 0).blink)) /\
         (h.ltail == e <==> is_null ((get h0 e 0).flink)) /\
         live h0 (get h0 e 0).blink /\
         live h0 (get h0 e 0).flink))
   (ensures (fun _ y h2 -> dlisthead_is_valid h2 y))
=
  if ptr_eq h.lhead e then ( // removing from the head of the list
    if ptr_eq h.ltail e then (// and removing from the tail - the list will now be empty
      { lhead = null; ltail = null; nodes = hide Seq.createEmpty }
    ) else (
      let next = (!*e).flink in
      next.(0ul) <- { next.(0ul) with blink = null; }; // e.flink.blink <- null
      admit ();
      { lhead = (!*e).flink; ltail = h.ltail; nodes = elift1 Seq.tail h.nodes }
    )
  ) else if ptr_eq h.ltail e then ( // removing from the tail of the list, but the list will be non-empty
    let prev = (!*e).blink in
    prev.(0ul) <- { prev.(0ul) with flink = null; }; // e.blink.flink <- null
    admit ();
    { lhead = h.lhead; ltail = (!*e).blink; nodes = elift1 fst (elift1 Seq.Properties.un_snoc h.nodes) }
  ) else ( // removing from the middle of the list
    let next = (!*e).flink in
    let prev = (!*e).blink in
    prev.(0ul) <- { prev.(0ul) with flink = next; };
    next.(0ul) <- { next.(0ul) with blink = prev; };
    admit ();
    h // TODO: Write down a { h with nodes = REMOVE !*e FROM h.nodes } here
  )

(** Insert e after prior, in list h *)
let insertEntryAfter (#t:Type) (h:dlisthead t) (prior:pointer (dlist t)) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if ptr_eq h.ltail prior then ( // appending to the end of the list
    insertTailList h e
  ) else (
    let next = (!*prior).flink in
    prior.(0ul) <- { prior.(0ul) with flink = e };
    e.(0ul) <- { e.(0ul) with blink=prior; flink=next };
    next.(0ul) <- { next.(0ul) with blink = e };
    h
  )

(** Insert e after next, in list h *)
let insertEntryBefore (#t:Type) (h:dlisthead t) (next:pointer (dlist t)) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if h.lhead = next then ( // adding to the front of the list
    insertHeadList h e
  ) else (
    let prior = (!*next).blink in
    prior.(0ul) <- { prior.(0ul) with flink = e };
    e.(0ul) <- { e.(0ul) with blink=prior; flink=next };
    next.(0ul) <- { next.(0ul) with blink = e };
    h
  )
*)
