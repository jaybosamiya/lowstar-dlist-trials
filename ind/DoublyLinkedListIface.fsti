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

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module L = FStar.List.Tot
module B = LowStar.Buffer

/// Abstract types defined by this library

(** A singular node which stores a value of type [a] *)
val node (a:Type0) : Type0

(** A doublylinkedlist of elements of type [a] *)
val dll (a:Type0) : Type0

/// Type aliases

(** Pointer to node *)
unfold let pnode (a:Type0) = B.pointer (node a)
(** Pointer to doubly linked list *)
unfold let pdll (a:Type0) = B.pointer (dll a)

/// Abstract Validity Predicates

val node_valid (h:HS.mem) (n:pnode 'a) : prop

val dll_valid (h:HS.mem) (d:pdll 'a) : prop

/// Getters and setters for [node]s

val g_node_val (h:HS.mem) (n:pnode 'a) : GTot 'a

val node_val (n:pnode 'a) :
  HST.StackInline 'a
    (requires (fun h0 -> node_valid h0 n))
    (ensures (fun h0 v h1 -> h0 == h1 /\ v == g_node_val h0 n))

val node_of (v:'a) :
  HST.StackInline (pnode 'a)
    (requires (fun h0 -> True))
    (ensures (fun h0 n h1 -> h0 == h1 /\ v == g_node_val h0 n)) // TODO: Check if these postconditions actually hold

/// Viewing ghostly state of a DoublyLinkedList as a list

val as_list (h:HS.mem) (d:pdll 'a) : GTot (list (pnode 'a))

/// Creating an empty DoublyLinkedList, and quickly accessing the head
/// and tail of a DoublyLinkedList

val dll_new (u:unit)  :
  HST.StackInline (pdll 'a)
    (requires (fun h0 -> True))
    (ensures (fun h0 d h1 ->
         h0 == h1 /\
         dll_valid h1 d /\
         as_list h1 d == [])) // TODO: Check if these postconditions actually hold

val dll_head (d:pdll 'a) :
  HST.StackInline (pnode 'a)
    (requires (fun h0 -> dll_valid h0 d /\ L.length (as_list h0 d) > 0))
    (ensures (fun h0 n h1 ->
         h0 == h1 /\
         dll_valid h1 d /\
         as_list h0 d == as_list h1 d /\
         n == L.hd (as_list h0 d))) // TODO: Check if these postconditions actually hold

val dll_tail (d:pdll 'a) :
  HST.StackInline (pnode 'a)
    (requires (fun h0 -> dll_valid h0 d /\ L.length (as_list h0 d) > 0))
    (ensures (fun h0 n h1 ->
         h0 == h1 /\
         dll_valid h1 d /\
         as_list h0 d == as_list h1 d /\
         n == snd (L.unsnoc (as_list h0 d)))) // TODO: Check if these postconditions actually hold

/// DoublyLinkedList operations on standard [list]s instead

let l_insert_start (l:list 'a) (x:'a) : GTot (list 'a) =
  x :: l

let l_insert_end (l:list 'a) (x:'a) : GTot (list 'a) =
  L.snoc (l, x)

let l_insert_before (x0:'a) (l:list 'a{x0 `L.memP` l}) (x:'a) : GTot (list 'a) =
  let l1, l2 = L.split_using l x0 in
  l1 `L.append` (x :: l2)

let l_insert_after (x0:'a) (l:list 'a{x0 `L.memP` l}) (x:'a) : GTot (list 'a) =
  let l1, x1 :: l2 = L.lemma_split_using l x0; L.split_using l x0 in
  assert (x0 == x1);
  l1 `L.append` (x0 :: (x :: l2))

let l_remove_start (l:list 'a{L.length l > 0}) : GTot (list 'a) =
  match l with
  | _ :: l' -> l'

let l_remove_end (l:list 'a{L.length l > 0}) : GTot (list 'a) =
  let l', _ = L.unsnoc l in
  l'

let l_remove_mid (l:list 'a{L.length l > 0}) (x:'a {x `L.memP` l}) : GTot (list 'a) =
  let l1, x0 :: l2 = L.lemma_split_using l x; L.split_using l x in
  assert (x == x0);
  l1 `L.append` l2

/// Footprint of nodes and lists

val fp_node (n:pnode 'a) : GTot B.loc
val fp_dll (d:pdll 'a) : GTot B.loc

/// Stateful DoublyLinkedList operations
///
/// These are most likely what you want to be using when writing
/// code. The rest of this interface lets you talk about these
/// operations easily.

val dll_insert_start (d:pdll 'a) (n:pnode 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ node_valid h0 n))
    (ensures (fun h0 () h1 ->
         B.modifies (B.loc_union (fp_dll d) (fp_node n)) h0 h1 /\
         dll_valid h1 d /\ node_valid h1 n /\
         g_node_val h0 n == g_node_val h1 n /\
         as_list h1 d == l_insert_start (as_list h0 d) n))

val dll_insert_end (d:pdll 'a) (n:pnode 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ node_valid h0 n))
    (ensures (fun h0 () h1 ->
         B.modifies (B.loc_union (fp_dll d) (fp_node n)) h0 h1 /\
         dll_valid h1 d /\ node_valid h1 n /\
         g_node_val h0 n == g_node_val h1 n /\
         as_list h1 d == l_insert_end (as_list h0 d) n))

val dll_insert_before (n':pnode 'a) (d:pdll 'a) (n:pnode 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ node_valid h0 n /\ n' `L.memP` as_list h0 d))
    (ensures (fun h0 () h1 ->
         B.modifies (B.loc_union (B.loc_union (fp_dll d) (fp_node n)) (fp_node n')) h0 h1 /\
         dll_valid h1 d /\ node_valid h1 n /\
         g_node_val h0 n == g_node_val h1 n /\
         g_node_val h0 n' == g_node_val h1 n' /\
         as_list h1 d == l_insert_before n' (as_list h0 d) n))

val dll_insert_after (n':pnode 'a) (d:pdll 'a) (n:pnode 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ node_valid h0 n /\ n' `L.memP` as_list h0 d))
    (ensures (fun h0 () h1 ->
         B.modifies (B.loc_union (B.loc_union (fp_dll d) (fp_node n)) (fp_node n')) h0 h1 /\
         dll_valid h1 d /\ node_valid h1 n /\
         g_node_val h0 n == g_node_val h1 n /\
         g_node_val h0 n' == g_node_val h1 n' /\
         as_list h1 d == l_insert_after n' (as_list h0 d) n))

val dll_remove_start (d:pdll 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ L.length (as_list h0 d) > 0))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll d) h0 h1 /\
         dll_valid h1 d /\
         as_list h1 d == l_remove_start (as_list h0 d)))

val dll_remove_end (d:pdll 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ L.length (as_list h0 d) > 0))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll d) h0 h1 /\
         dll_valid h1 d /\
         as_list h1 d == l_remove_end (as_list h0 d)))

val dll_remove_mid (d:pdll 'a) (n:pnode 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ n `L.memP` as_list h0 d))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll d) h0 h1 /\
         dll_valid h1 d /\
         as_list h1 d == l_remove_mid (as_list h0 d) n))

/// Automatic validity maintenance
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.

val dll_remains_valid_upon_staying_unchanged (h0 h1:HS.mem) (l:B.loc) (d:pdll 'a) :
  Lemma
    (requires (dll_valid h0 d /\
               B.modifies l h0 h1 /\
               B.loc_disjoint (fp_dll d) l))
    (ensures (dll_valid h1 d))
    [SMTPat (dll_valid h0 d); SMTPat (dll_valid h1 d); SMTPat (B.loc_disjoint (fp_dll d) l)]

val node_remains_valid_upon_staying_unchanged (h0 h1:HS.mem) (l:B.loc) (n:pnode 'a) :
  Lemma
    (requires (node_valid h0 n /\
               B.modifies l h0 h1 /\
               B.loc_disjoint (fp_node n) l))
    (ensures (node_valid h1 n))
    [SMTPat (node_valid h0 n); SMTPat (node_valid h1 n); SMTPat (B.loc_disjoint (fp_node n) l)]

/// Properties of nodes inside and outside lists
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.

// TODO: Write about the following
// + If node is in valid list, it is also valid
// + If node is in list, fp is included
// + If node is not in list, fp is disjoint
