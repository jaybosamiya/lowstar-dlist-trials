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

let node a = DLL.node a
let dll a = DLL.dll a

/// Abstract Validity Predicates

let node_valid h n = True /\ B.live h n // XXX: why do I need the True here?

let dll_valid h d =
  B.live h d /\
  DLL.dll_valid h (d@h)

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

/// Auxiliary useful lemma: If a dll is valid, then all nodes inside
/// it are valid. Should auto-trigger at the right places.

let _auto_dll_valid_implies_node_valid (h:HS.mem) (d:pdll 'a) (n:pnode 'a) :
  Lemma
    (requires (dll_valid h d /\ n `L.memP` as_list h d))
    (ensures (node_valid h n))
    [SMTPat (dll_valid h d);
     SMTPat (node_valid h n);
     SMTPat (n `L.memP` as_list h d)] =
  let pos = L.index_of (as_list h d) n in
  DLL.extract_nodelist_contained h (as_list h d) pos

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

/// Footprint of nodes and lists

let fp_node n = B.loc_buffer n

let fp_dll d = B.loc_buffer d

/// Stateful DoublyLinkedList operations
///
/// These are most likely what you want to be using when writing
/// code. The rest of this interface lets you talk about these
/// operations easily.

let dll_insert_start d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_at_head (!*d) n

let dll_insert_end d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_at_tail (!*d) n

let dll_insert_before n' d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_before (!*d) n' n

let dll_insert_after n' d n =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_insert_after (!*d) n' n

let dll_remove_start d =
  admit (); // TODO: Need to prove a bunch of things to make this happen
  d *= DLL.dll_remove_head (!*d)

let dll_remove_end d =
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

let dll_remains_valid_upon_staying_unchanged h0 h1 l d =
  admit () // TODO: Need to prove a bunch of things to make this happen

let node_remains_valid_upon_staying_unchanged h0 h1 l n =
  admit () // TODO: Need to prove a bunch of things to make this happen
