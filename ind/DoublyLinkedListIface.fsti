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

/// Abstract Validity Predicates

val node_valid (h:HS.mem) (n:node 'a) : prop

val dll_valid (h:HS.mem) (d:dll 'a) : prop

/// Getters and setters for [node]s

val g_node_val (h:HS.mem) (n:node 'a) : GTot 'a

val node_val (n:node 'a) :
  HST.StackInline 'a
    (requires (fun h0 -> node_valid h0 n))
    (ensures (fun h0 v h1 -> h0 == h1 /\ v == g_node_val h0 n))

val node_of (v:'a) :
  HST.StackInline (node 'a)
    (requires (fun h0 -> True))
    (ensures (fun h0 n h1 ->
         B.modifies B.loc_none h0 h1 /\
         v == g_node_val h1 n))

/// Viewing ghostly state of a DoublyLinkedList as a list

val as_list (h:HS.mem) (d:dll 'a) : GTot (list (node 'a))

/// Creating an empty DoublyLinkedList, and quickly accessing the head
/// and tail of a DoublyLinkedList

val dll_new (u:unit)  :
  HST.StackInline (dll 'a)
    (requires (fun h0 -> True))
    (ensures (fun h0 d h1 ->
         B.modifies B.loc_none h0 h1 /\
         dll_valid h1 d /\
         as_list h1 d == []))

val dll_head (d:dll 'a) :
  HST.StackInline (node 'a)
    (requires (fun h0 -> dll_valid h0 d /\ L.length (as_list h0 d) > 0))
    (ensures (fun h0 n h1 ->
         B.modifies B.loc_none h0 h1 /\
         dll_valid h1 d /\
         node_valid h1 n /\
         as_list h0 d == as_list h1 d /\
         n == L.hd (as_list h0 d)))

val dll_tail (d:dll 'a) :
  HST.StackInline (node 'a)
    (requires (fun h0 -> dll_valid h0 d /\ L.length (as_list h0 d) > 0))
    (ensures (fun h0 n h1 ->
         h0 == h1 /\
         dll_valid h1 d /\
         node_valid h1 n /\
         as_list h0 d == as_list h1 d /\
         n == snd (L.unsnoc (as_list h0 d))))

/// DoublyLinkedList operations on standard [list]s instead

let l_insert_at_head (l:list 'a) (x:'a) : GTot (list 'a) =
  x :: l

let l_insert_at_tail (l:list 'a) (x:'a) : GTot (list 'a) =
  L.snoc (l, x)

let l_insert_before (x0:'a) (l:list 'a{x0 `L.memP` l}) (x:'a) : GTot (list 'a) =
  let l1, l2 = L.split_using l x0 in
  l1 `L.append` (x :: l2)

let l_insert_after (x0:'a) (l:list 'a{x0 `L.memP` l}) (x:'a) : GTot (list 'a) =
  let l1, x1 :: l2 = L.lemma_split_using l x0; L.split_using l x0 in
  assert (x0 == x1);
  l1 `L.append` (x0 :: (x :: l2))

let l_remove_head (l:list 'a{L.length l > 0}) : GTot (list 'a) =
  match l with
  | _ :: l' -> l'

let l_remove_tail (l:list 'a{L.length l > 0}) : GTot (list 'a) =
  let l', _ = L.unsnoc l in
  l'

let l_remove_mid (l:list 'a{L.length l > 0}) (x:'a {x `L.memP` l}) : GTot (list 'a) =
  let l1, x0 :: l2 = L.lemma_split_using l x; L.split_using l x in
  assert (x == x0);
  l1 `L.append` l2

/// Abstract node and list footprints

val fp_node (n:node 'a) : GTot B.loc

val fp_dll (h:HS.mem) (d:dll 'a) : GTot B.loc

/// Stateful DoublyLinkedList operations
///
/// These are most likely what you want to be using when writing
/// code. The rest of this interface lets you talk about these
/// operations easily.

// TODO: Connect [fp_dll h0 d] and [fp_dll h1 d] in these.
// TODO: Check if the modifies clauses are correct.

val dll_insert_at_head (d:dll 'a) (n:node 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ node_valid h0 n))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll h0 d) h0 h1 /\
         dll_valid h1 d /\ node_valid h1 n /\
         g_node_val h0 n == g_node_val h1 n /\
         as_list h1 d == l_insert_at_head (as_list h0 d) n))

val dll_insert_at_tail (d:dll 'a) (n:node 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ node_valid h0 n))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll h0 d) h0 h1 /\
         dll_valid h1 d /\ node_valid h1 n /\
         g_node_val h0 n == g_node_val h1 n /\
         as_list h1 d == l_insert_at_tail (as_list h0 d) n))

val dll_insert_before (n':node 'a) (d:dll 'a) (n:node 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ node_valid h0 n /\ n' `L.memP` as_list h0 d))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll h0 d) h0 h1 /\
         dll_valid h1 d /\ node_valid h1 n /\
         g_node_val h0 n == g_node_val h1 n /\
         g_node_val h0 n' == g_node_val h1 n' /\
         as_list h1 d == l_insert_before n' (as_list h0 d) n))

val dll_insert_after (n':node 'a) (d:dll 'a) (n:node 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ node_valid h0 n /\ n' `L.memP` as_list h0 d))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll h0 d) h0 h1 /\
         dll_valid h1 d /\ node_valid h1 n /\
         g_node_val h0 n == g_node_val h1 n /\
         g_node_val h0 n' == g_node_val h1 n' /\
         as_list h1 d == l_insert_after n' (as_list h0 d) n))

val dll_remove_head (d:dll 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ L.length (as_list h0 d) > 0))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll h0 d) h0 h1 /\
         dll_valid h1 d /\
         as_list h1 d == l_remove_head (as_list h0 d)))

val dll_remove_tail (d:dll 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ L.length (as_list h0 d) > 0))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll h0 d) h0 h1 /\
         dll_valid h1 d /\
         as_list h1 d == l_remove_tail (as_list h0 d)))

val dll_remove_mid (d:dll 'a) (n:node 'a) :
  HST.Stack unit
    (requires (fun h0 -> dll_valid h0 d /\ n `L.memP` as_list h0 d))
    (ensures (fun h0 () h1 ->
         B.modifies (fp_dll h0 d) h0 h1 /\
         dll_valid h1 d /\
         as_list h1 d == l_remove_mid (as_list h0 d) n))

/// Automatic validity maintenance
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.

// val dll_remains_valid_upon_staying_unchanged (h0 h1:HS.mem) (l:B.loc) (d:dll 'a) :
//   Lemma
//     (requires (dll_valid h0 d /\
//                B.modifies l h0 h1 /\
//                B.loc_disjoint (fp_dll h0 d) l))
//     (ensures (dll_valid h1 d))
//     [SMTPat (dll_valid h0 d); SMTPat (dll_valid h1 d); SMTPat (B.loc_disjoint (fp_dll h0 d) l)]

// val node_remains_valid_upon_staying_unchanged (h0 h1:HS.mem) (l:B.loc) (n:node 'a) :
//   Lemma
//     (requires (node_valid h0 n /\
//                B.modifies l h0 h1 /\
//                B.loc_disjoint (fp_node h0 n) l))
//     (ensures (node_valid h1 h0 n))
//     [SMTPat (node_valid h0 n); SMTPat (node_valid h1 n); SMTPat (B.loc_disjoint (fp_node n) l)]

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
