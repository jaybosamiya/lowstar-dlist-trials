(*
   Copyright 2018 Jay Bosamiya

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module DoublyLinkedListIface

/// This module consists of proofs / code for the iface that is
/// written in the actual fsti. Most of this code will never be user
/// facing, and will soon be merged into the DoublyLinkedList module,
/// as I work on moving stuff into DoublLinkedList.fsti from the iface
/// fsti.

module DLL = DoublyLinkedList

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module G = FStar.Ghost
module L = FStar.List.Tot
module B = LowStar.Buffer

open LowStar.BufferOps

/// Convenience operators

unfold let (@) (a:B.pointer 't) (h0:HS.mem) = B.get h0 a 0
unfold let (^@) (a:B.pointer_or_null 't{a =!= B.null}) (h0:HS.mem) = B.get h0 a 0

/// Abstract types defined by this library
///
/// Note: Somehow confusingly, a node in the iface is a pointer to a
/// real node, and a dll in the iface is a pointer to a real
/// dll. Fortunately though, most users of the library will never even
/// be looking inside the implementation, and thus hopefully it won't
/// be confusing.

let node a = B.pointer (DLL.node a)
let dll a = B.pointer (DLL.dll a)

/// Abstract Validity Predicates

let node_valid h n = True /\ B.live h n // XXX: why do I need the True here?

let dll_valid h d =
  B.live h d /\
  DLL.dll_valid h (d@h) /\
  B.loc_buffer d `B.loc_disjoint` DLL.dll_fp0 (d@h)

/// Abstract node and list footprints

let fp_node n = B.loc_buffer n

let fp_dll h d =
  B.loc_union (B.loc_buffer d) (DLL.dll_fp0 (d@h)) // TODO: Fix this

/// Getters and setters for [node]s

let g_node_val h n =
  (n@h).DLL.p

let node_val n =
  (!*n).DLL.p

let node_of v =
  B.alloca (DLL.empty_node v) 1ul

/// Abstract Predicate to help "recall" that [g_node_val] remains
/// unchanged for nodes, across multiple [mem]s

let _aux_unchanged_node_vals t h0 h1 (n:node t) =
  (B.live h0 n ==>
   (g_node_val h0 n == g_node_val h1 n /\ B.live h1 n))

let unchanged_node_vals t h0 h1 =
  (forall (n:node t). {:pattern (g_node_val h1 n) \/ (B.live h1 n)}
     _aux_unchanged_node_vals t h0 h1 n)

/// Viewing ghostly state of a list

let as_list h d =
  G.reveal (d@h).DLL.nodes

/// Creating an empty DoublyLinkedList, and quickly accessing the head
/// and tail of a DoublyLinkedList

let dll_new () =
  B.alloca DLL.empty_list 1ul

let dll_head d =
  (!*d).DLL.lhead

let dll_tail d =
  let h0 = HST.get () in
  L.lemma_unsnoc_is_last (as_list h0 d);
  (!*d).DLL.ltail

/// Useful auxiliary lemmas

(** If a node is inside a valid list, then the node is valid. *)
val lemma_node_in_valid_dll_is_valid (h:HS.mem) (d:dll 'a) (n:node 'a) :
  Lemma
    (requires (dll_valid h d /\ n `L.memP` as_list h d))
    (ensures (node_valid h n))
let lemma_node_in_valid_dll_is_valid h d n =
  let pos = L.index_of (as_list h d) n in
  DLL.extract_nodelist_contained h (as_list h d) pos

(** Aux lemma *)
val _lemma_nodelist_contained_in_unmodified_mem (h0 h1:HS.mem) (s:B.loc) (nl:list (node 'a)) :
  Lemma
    (requires (B.modifies s h0 h1 /\
               B.loc_disjoint s (DLL.nodelist_fp0 nl) /\
              (DLL.nodelist_contained0 h0 nl)))
    (ensures (DLL.nodelist_contained0 h1 nl))
let rec _lemma_nodelist_contained_in_unmodified_mem h0 h1 s nl =
  match nl with
  | [] -> ()
  | n :: ns ->
    _lemma_nodelist_contained_in_unmodified_mem h0 h1 s ns

(** Aux lemma *)
val _lemma_nodelist_conn_in_unmodified_mem (h0 h1:HS.mem) (s:B.loc) (nl:list (node 'a)) :
  Lemma
    (requires (B.modifies s h0 h1 /\
               B.loc_disjoint s (DLL.nodelist_fp0 nl) /\
               DLL.nodelist_contained0 h0 nl /\
              (DLL.nodelist_conn h0 nl)))
    (ensures (DLL.nodelist_conn h1 nl))
let rec _lemma_nodelist_conn_in_unmodified_mem h0 h1 s nl =
  match nl with
  | [] -> ()
  | n1 :: rest -> match rest with
    | [] -> ()
    | n2 :: ns ->
      _lemma_nodelist_conn_in_unmodified_mem h0 h1 s rest

(** Aux lemma *)
val _lemma_nodelist_disjoint_in_push (h0 h1:HS.mem) (nl:list (node 'a)) :
  Lemma
    (requires (HS.fresh_frame h0 h1 /\
               DLL.nodelist_contained0 h0 nl))
    (ensures (DLL.nodelist_fp0 nl `B.loc_disjoint` (B.loc_region_only false (HS.get_tip h1))))
let rec _lemma_nodelist_disjoint_in_push h0 h1 nl =
  match nl with
  | [] -> ()
  | n :: ns ->
    _lemma_nodelist_disjoint_in_push h0 h1 ns

(** If a new frame is pushed, then a dll remains valid and unchanged. *)
val _auto_dll_valid_and_unchanged_through_push (h0 h1:HS.mem) (d:dll 'a) :
  Lemma
    (requires (dll_valid h0 d /\ HS.fresh_frame h0 h1))
    (ensures (dll_valid h1 d /\ d@h0 == d@h1))
    [SMTPat (dll_valid h0 d);
     SMTPat (HS.fresh_frame h0 h1)]
let _auto_dll_valid_and_unchanged_through_push h0 h1 d =
  B.fresh_frame_modifies h0 h1;
  _lemma_nodelist_contained_in_unmodified_mem h0 h1 B.loc_none (as_list h1 d);
  _lemma_nodelist_conn_in_unmodified_mem h0 h1 B.loc_none (as_list h1 d)

(** If a frame is popped, then a dll remains valid and unchanged. *)
val _auto_dll_valid_and_unchanged_through_pop (h0 h1:HS.mem) (d:dll 'a) :
  Lemma
    (requires (dll_valid h0 d /\ HS.popped h0 h1 /\
              B.loc_disjoint (fp_dll h0 d) (B.loc_all_regions_from false (HS.get_tip h0))))
    (ensures (dll_valid h1 d /\ d@h0 == d@h1))
    [SMTPat (dll_valid h0 d);
     SMTPat (HS.popped h0 h1)]
let _auto_dll_valid_and_unchanged_through_pop h0 h1 d =
  B.popped_modifies h0 h1;
  assert (B.loc_all_regions_from false (HS.get_tip h0) `B.loc_includes`
            B.loc_region_only false (HS.get_tip h0)); // OBSERVE
  let loc = B.loc_region_only false (HS.get_tip h0) in
  _lemma_nodelist_contained_in_unmodified_mem h0 h1 loc (as_list h1 d);
  _lemma_nodelist_conn_in_unmodified_mem h0 h1 loc (as_list h1 d)

(** If stack discipline is followed, then a valid modification inside
    a push-pop pair is also valid outside of it. *)
val _auto_dll_modified_with_push_pop (h0 h1:HS.mem) (d:dll 'a) (h2 h3:HS.mem) :
  Lemma
    (requires (dll_valid h0 d /\
               HS.fresh_frame h0 h1 /\
               B.modifies (B.loc_union (fp_dll h0 d) (fp_dll h3 d)) h1 h2 /\
               B.loc_disjoint (fp_dll h0 d) (B.loc_region_only false (HS.get_tip h2)) /\
               B.loc_disjoint (fp_dll h3 d) (B.loc_region_only false (HS.get_tip h2)) /\
               HS.get_tip h1 == HS.get_tip h2 /\
               dll_valid h2 d /\
               HS.popped h2 h3))
    (ensures (dll_valid h3 d))
    [SMTPat (HS.fresh_frame h0 h1);
     SMTPat (HS.popped h2 h3);
     SMTPat (dll_valid h3 d)]
let _auto_dll_modified_with_push_pop h0 h1 d h2 h3 =
  let loc = B.loc_region_only false (HS.get_tip h2) in
  B.popped_modifies h2 h3;
  _lemma_nodelist_contained_in_unmodified_mem h2 h3 loc (as_list h3 d);
  _lemma_nodelist_conn_in_unmodified_mem h2 h3 loc (as_list h3 d)

(** If a new frame is pushed, the the dll's fp is disjoint from what just got pushed. *)
val _auto_dll_fp_disjoint_from_push (h0 h1:HS.mem) (d:dll 'a) :
  Lemma
    (requires (dll_valid h0 d /\ HS.fresh_frame h0 h1))
    (ensures (B.loc_disjoint (fp_dll h0 d) (B.loc_region_only false (HS.get_tip h1))))
    [SMTPat (dll_valid h0 d);
     SMTPat (HS.fresh_frame h0 h1)]
let _auto_dll_fp_disjoint_from_push h0 h1 d =
  _lemma_nodelist_disjoint_in_push h0 h1 (G.reveal (d@h0).DLL.nodes)

(** If a valid dll is placed into a pointer, it stays valid *)
val _auto_dll_assign_valid_stays_valid (h0 h1:HS.mem) (d:dll 'a) (d2:DLL.dll 'a) :
  Lemma
    (requires (DLL.dll_valid h0 d2 /\
               B.modifies (B.loc_buffer d) h0 h1 /\
               B.loc_buffer d `B.loc_disjoint` DLL.dll_fp0 d2 /\
               B.live h0 d /\
               d@h1 == d2))
    (ensures (dll_valid h1 d))
    [SMTPat (DLL.dll_valid h0 d2);
     SMTPat (B.modifies (B.loc_buffer d) h0 h1);
     SMTPat (dll_valid h1 d)]
let _auto_dll_assign_valid_stays_valid h0 h1 d d2 =
  _lemma_nodelist_conn_in_unmodified_mem h0 h1 (B.loc_buffer d) (G.reveal d2.DLL.nodes);
  _lemma_nodelist_contained_in_unmodified_mem h0 h1 (B.loc_buffer d) (G.reveal d2.DLL.nodes)

(** If [unchanged_node_vals] is true, then it remains true through a push-pop. *)
val _auto_unchanged_node_vals_through_push_pop (h0 h1:HS.mem) (t:Type0) (h2 h3:HS.mem) :
  Lemma
    (requires (unchanged_node_vals t h1 h2 /\
               HS.fresh_frame h0 h1 /\ HS.popped h2 h3 /\
               HS.get_tip h1 == HS.get_tip h2))
    (ensures (unchanged_node_vals t h0 h3))
    [SMTPat (unchanged_node_vals t h0 h3);
     SMTPat (HS.fresh_frame h0 h1);
     SMTPat (HS.popped h2 h3)]
let _auto_unchanged_node_vals_through_push_pop h0 h1 t h2 h3 =
  // assert (unchanged_node_vals t h0 h1);
  let loc = B.loc_region_only false (HS.get_tip h2) in
  B.popped_modifies h2 h3;
  FStar.Classical.forall_intro_sub #_ #(_aux_unchanged_node_vals t h0 h3)
    (fun n -> assert (_aux_unchanged_node_vals t h0 h2 n)) // OBSERVE

/// Moving forwards or backwards in a list

let next_node d n =
  let h0 = HST.get () in
  lemma_node_in_valid_dll_is_valid h0 d n;
  DLL.extract_nodelist_conn h0 (as_list h0 d) (L.index_of (as_list h0 d) n);
  (!*n).DLL.flink

let prev_node d n =
  let h0 = HST.get () in
  lemma_node_in_valid_dll_is_valid h0 d n;
  DLL.extract_nodelist_conn h0 (as_list h0 d) (L.index_of (as_list h0 d) n - 1);
  (!*n).DLL.blink

/// Stateful DoublyLinkedList operations
///
/// These are most likely what you want to be using when writing
/// code. The rest of this interface lets you talk about these
/// operations easily.

#set-options "--z3rlimit 20 --max_fuel 2 --max_ifuel 1"

let dll_insert_at_head #t d n =
  HST.push_frame ();
  let h0 = HST.get () in
  d *= DLL.dll_insert_at_head (!*d) n;
  let h1 = HST.get () in
  assume (unchanged_node_vals t h0 h1);
  HST.pop_frame ()

#reset-options

let dll_insert_at_tail #t d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_at_tail (!*d) n

let dll_insert_before #t n' d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_before (!*d) n' n

let dll_insert_after #t n' d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_after (!*d) n' n

let dll_remove_head #t d =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_remove_head (!*d)

let dll_remove_tail #t d =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_remove_tail (!*d)

let dll_remove_mid #t d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_remove_node (!*d) n

/// Automatic validity maintenance
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.

// let dll_remains_valid_upon_staying_unchanged h0 h1 l d =
//   admit () // TODO: Need to prove a bunch of things to make this happen

// let node_remains_valid_upon_staying_unchanged h0 h1 l n =
//   admit () // TODO: Need to prove a bunch of things to make this happen

/// Properties of nodes inside and outside lists
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.
