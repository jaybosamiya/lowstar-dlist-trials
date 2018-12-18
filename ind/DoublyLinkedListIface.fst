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
  DLL.dll_valid h (d@h)

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
val _lemma_nodelist_contained_in_unmodified_mem (h0 h1:HS.mem) (nl:list (node 'a)) :
  Lemma
    (requires (B.modifies B.loc_none h0 h1 /\
              (DLL.nodelist_contained0 h0 nl)))
    (ensures (DLL.nodelist_contained0 h1 nl))
let rec _lemma_nodelist_contained_in_unmodified_mem h0 h1 nl =
  match nl with
  | [] -> ()
  | n :: ns ->
    _lemma_nodelist_contained_in_unmodified_mem h0 h1 ns

(** Aux lemma *)
val _lemma_nodelist_conn_in_unmodified_mem (h0 h1:HS.mem) (nl:list (node 'a)) :
  Lemma
    (requires (B.modifies B.loc_none h0 h1 /\
               DLL.nodelist_contained0 h0 nl /\
              (DLL.nodelist_conn h0 nl)))
    (ensures (DLL.nodelist_conn h1 nl))
let rec _lemma_nodelist_conn_in_unmodified_mem h0 h1 nl =
  match nl with
  | [] -> ()
  | n1 :: rest -> match rest with
    | [] -> ()
    | n2 :: ns ->
      _lemma_nodelist_conn_in_unmodified_mem h0 h1 rest

(** If a new frame is pushed, then a dll remains valid and unchanged. *)
val _auto_dll_valid_and_unchanged_through_push (h0 h1:HS.mem) (d:dll 'a) :
  Lemma
    (requires (dll_valid h0 d /\ HS.fresh_frame h0 h1))
    (ensures (dll_valid h1 d /\ d@h0 == d@h1))
    [SMTPat (dll_valid h0 d);
     SMTPat (HS.fresh_frame h0 h1)]
let _auto_dll_valid_and_unchanged_through_push h0 h1 d =
  B.fresh_frame_modifies h0 h1;
  _lemma_nodelist_contained_in_unmodified_mem h0 h1 (as_list h1 d);
  _lemma_nodelist_conn_in_unmodified_mem h0 h1 (as_list h1 d)

// TODO: Figure out for pop

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

let dll_insert_at_head d n =
  HST.push_frame ();
  let h0 = HST.get () in
  d *= DLL.dll_insert_at_head (!*d) n;
  let h1 = HST.get () in
  assume (B.modifies (fp_dll h1 d) h0 h1);
  assume (fp_dll h1 d == B.loc_union (fp_dll h0 d) (fp_node n));
  assume (dll_valid h1 d);
  assume (g_node_val h0 n == g_node_val h1 n);
  assume (as_list h1 d == l_insert_at_head (as_list h0 d) n);
  assume (HST.equal_domains h0 h1);
  HST.pop_frame ();
  admit ()

let dll_insert_at_tail d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_at_tail (!*d) n

let dll_insert_before n' d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_before (!*d) n' n

let dll_insert_after n' d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_after (!*d) n' n

let dll_remove_head d =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_remove_head (!*d)

let dll_remove_tail d =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_remove_tail (!*d)

let dll_remove_mid d n =
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
