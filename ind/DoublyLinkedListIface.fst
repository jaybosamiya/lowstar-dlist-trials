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
  B.loc_union (B.loc_buffer d) (DLL.dll_fp0 (d@h))

/// Getters and setters for [node]s

let g_node_val h n =
  (n@h).DLL.p

let node_val n =
  (!*n).DLL.p

let node_of v =
  B.alloca (DLL.empty_node v) 1ul

/// Abstract Predicate to help "recall" that [g_node_val] remains
/// unchanged for nodes, across multiple [mem]s

let unchanged_node_val h0 h1 n =
  (B.live h0 n ==>
   (g_node_val h0 n == g_node_val h1 n /\ B.live h1 n))

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
val _lemma_dll_valid_and_unchanged_through_pop (h0 h1:HS.mem) (d:dll 'a) :
  Lemma
    (requires (dll_valid h0 d /\ HS.popped h0 h1 /\
              B.loc_disjoint (fp_dll h0 d) (B.loc_all_regions_from false (HS.get_tip h0))))
    (ensures (dll_valid h1 d /\ d@h0 == d@h1))
let _lemma_dll_valid_and_unchanged_through_pop h0 h1 d =
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

(** [unchanged_node_vals] is transitive *)
let rec _lemma_unchanged_node_vals_transitive (h0 h1 h2:HS.mem) (ns:list (node 'a)) :
  Lemma
    (requires (
        (unchanged_node_vals h0 h1 ns) /\
        (unchanged_node_vals h1 h2 ns)))
    (ensures (
        (unchanged_node_vals h0 h2 ns))) =
  match ns with
  | [] -> ()
  | _ :: ns' -> _lemma_unchanged_node_vals_transitive h0 h1 h2 ns'

(** Auxiliary predicate: node list is disjoint from region *)
let rec _pred_nl_disjoint (h:HS.mem) (ns:list (node 'a)) =
  DLL.nodelist_fp0 ns `B.loc_disjoint` B.loc_region_only false (HS.get_tip h)

(** If [unchanged_node_vals] is true, then it remains true through a push-pop. *)
val _auto_unchanged_node_vals_through_push_pop (h0 h1:HS.mem) (ns:list (node 'a)) (h2 h3:HS.mem) :
  Lemma
    (requires (unchanged_node_vals h1 h2 ns /\
               HS.fresh_frame h0 h1 /\ HS.popped h2 h3 /\
               _pred_nl_disjoint h1 ns /\
               HS.get_tip h1 == HS.get_tip h2))
    (ensures (
        unchanged_node_vals h0 h1 ns /\ // used only for proof. not necessary outside
        unchanged_node_vals h2 h3 ns /\ // used only for proof. not necessary outside
        unchanged_node_vals h0 h3 ns))
    [SMTPat (unchanged_node_vals h0 h3 ns);
     SMTPat (HS.fresh_frame h0 h1);
     SMTPat (HS.popped h2 h3)]
let rec _auto_unchanged_node_vals_through_push_pop h0 h1 ns h2 h3 =
  match ns with
  | [] -> ()
  | n :: ns' ->
    _auto_unchanged_node_vals_through_push_pop h0 h1 ns' h2 h3;
    // assert (unchanged_node_vals h0 h1 ns);
    // assert (unchanged_node_vals h2 h3 ns);
    B.popped_modifies h2 h3

(** If a valid dll has a frame pushed, [_pred_nl_disjoint] stays true *)
val _auto_pred_nl_disjoint_push (h0 h1:HS.mem) (d:dll 'a) :
  Lemma
    (requires (dll_valid h0 d /\ HS.fresh_frame h0 h1))
    (ensures (_pred_nl_disjoint h1 (as_list h1 d)))
    [SMTPat (dll_valid h0 d);
     SMTPat (HS.fresh_frame h0 h1)]
let _auto_pred_nl_disjoint_push h0 h1 d =
  let loc = B.loc_region_only false (HS.get_tip h1) in
  let rec aux (ns:list (node 'a)) :
    Lemma
      (requires (DLL.nodelist_contained h0 ns /\ HS.fresh_frame h0 h1))
      (ensures (_pred_nl_disjoint h1 ns)) =
    match ns with
    | [] -> ()
    | n :: ns' -> aux ns'
  in
  aux (as_list h0 d)

(** The impl version of [unchanged_node_vals] is same as iface one *)
let rec _auto_unchanged_node_vals_DLL (h0 h1:HS.mem) (ns:list (node 'a)) :
  Lemma
    (requires (DLL.unchanged_node_vals h0 h1 ns))
    (ensures (unchanged_node_vals h0 h1 ns))
    [SMTPat (unchanged_node_vals h0 h1 ns)] =
  match ns with
  | [] -> ()
  | _ :: ns' -> _auto_unchanged_node_vals_DLL h0 h1 ns'

(** If a valid dll is placed into a pointer, its nodes stay unchanged *)
val _auto_unchanged_node_vals_stays_valid (h0 h1:HS.mem) (d:dll 'a) (d2:DLL.dll 'a) :
  Lemma
    (requires (DLL.dll_valid h0 d2 /\
               B.modifies (B.loc_buffer d) h0 h1 /\
               B.loc_buffer d `B.loc_disjoint` DLL.dll_fp0 d2 /\
               B.live h0 d /\
               d@h1 == d2))
    (ensures (unchanged_node_vals h0 h1 (as_list h1 d)))
    [SMTPat (DLL.dll_valid h0 d2);
     SMTPat (B.modifies (B.loc_buffer d) h0 h1);
     SMTPat (unchanged_node_vals h0 h1 (as_list h1 d))]
let _auto_unchanged_node_vals_stays_valid h0 h1 d d2 =
  let rec aux nl : Lemma
    (requires (
       B.modifies (B.loc_buffer d) h0 h1 /\
       DLL.nodelist_fp0 nl `B.loc_disjoint` B.loc_buffer d))
    (ensures (unchanged_node_vals h0 h1 nl)) =
    match nl with
    | [] -> ()
    | n :: ns -> aux ns in
  aux (as_list h1 d)

(** If a dll is assigned to, its original nodes stay unchanged *)
val _lemma_unchanged_node_vals_stays_valid0 (h0 h1:HS.mem) (d:dll 'a) :
  Lemma
    (requires (B.modifies (B.loc_buffer d) h0 h1 /\
               B.loc_buffer d `B.loc_disjoint` DLL.dll_fp0 (d@h0) /\
               B.live h0 d))
    (ensures (unchanged_node_vals h0 h1 (as_list h0 d)))
let _lemma_unchanged_node_vals_stays_valid0 h0 h1 d =
  let rec aux nl : Lemma
    (requires (
       B.modifies (B.loc_buffer d) h0 h1 /\
       DLL.nodelist_fp0 nl `B.loc_disjoint` B.loc_buffer d))
    (ensures (unchanged_node_vals h0 h1 nl)) =
    match nl with
    | [] -> ()
    | n :: ns -> aux ns in
  aux (as_list h0 d)

(** If a node belongs to a dll, then its fp is included *)
let rec _lemma_node_in_list_is_included (n:node 'a) (nl:list (node 'a)) :
  Lemma
    (requires (n `L.memP` nl))
    (ensures (DLL.nodelist_fp0 nl `B.loc_includes` fp_node n)) =
  match nl with
  | [_] -> ()
  | n' :: ns ->
    FStar.Classical.or_elim #_ #_ #(fun () -> DLL.nodelist_fp0 nl `B.loc_includes` fp_node n)
      (fun (_:unit{n == n'}) -> ())
      (fun (_:unit{n =!= n'}) -> _lemma_node_in_list_is_included n ns)

(** If a node_or_null is null or belongs to a dll, then its fp is included *)
let _lemma_node_in_list_or_null_is_included (n:B.pointer_or_null (DLL.node 'a)) (nl:list (node 'a)) :
  Lemma
    (requires (n =!= B.null ==> n `L.memP` nl))
    (ensures (DLL.nodelist_fp0 nl `B.loc_includes` B.loc_buffer n)) =
  FStar.Classical.arrow_to_impl
  #(n =!= B.null) #(DLL.nodelist_fp0 nl `B.loc_includes` B.loc_buffer n)
    (fun _ -> _lemma_node_in_list_is_included n nl)

(** If a node is in the list, then the node before it is also in the list if it is not null *)
let _lemma_prev_node_in_list (h:HS.mem) (n:node 'a) (d:dll 'a) :
  Lemma
    (requires (dll_valid h d /\ n `L.memP` as_list h d))
    (ensures (let n' = (n@h).DLL.blink in
              n' =!= B.null ==> n' `L.memP` as_list h d)) =
  let n' = (n@h).DLL.blink in
  let l = as_list h d in
  FStar.Classical.arrow_to_impl
  #(n' =!= B.null) #(n' =!= B.null /\ n' `L.memP` l)
  (fun _ ->
    lemma_node_in_valid_dll_is_valid h d n;
    DLL.extract_nodelist_conn h l (L.index_of l n - 1))

(** If a node is in the list, then the node after it is also in the list if it is not null *)
let _lemma_next_node_in_list (h:HS.mem) (n:node 'a) (d:dll 'a) :
  Lemma
    (requires (dll_valid h d /\ n `L.memP` as_list h d))
    (ensures (let n' = (n@h).DLL.flink in
              n' =!= B.null ==> n' `L.memP` as_list h d)) =
  let n' = (n@h).DLL.flink in
  let l = as_list h d in
  FStar.Classical.arrow_to_impl
  #(n' =!= B.null) #(n' =!= B.null /\ n' `L.memP` l)
  (fun _ ->
    lemma_node_in_valid_dll_is_valid h d n;
    L.lemma_unsnoc_is_last l;
    DLL.extract_nodelist_conn h l (L.index_of l n))

(** Insertion operations maintain membership *)
let rec _lemma_insertion_maintains_memP (l1 l2:list 'a) (x0 x1 x:'a) :
  Lemma
    (requires ((x0 `L.memP` l1) /\
               ((l2 == DLL._l_insert_before x0 l1 x1) \/
                (l2 == DLL._l_insert_after x0 l1 x1)) /\
               x `L.memP` l1))
    (ensures (x `L.memP` l2)) =
  match l1 with
  | [_] -> ()
  | x0' :: l1' ->
    FStar.Classical.or_elim #_ #_ #(fun () -> x `L.memP` l2)
      (fun (_:unit{x0' == x0 \/ x0' == x}) -> ())
      (fun (_:unit{x0' =!= x0 /\ x0' =!= x}) ->
         _lemma_insertion_maintains_memP l1' (L.tl l2) x0 x1 x)

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
  let y = DLL.dll_insert_at_head (!*d) n in
  let h' = HST.get () in
  d *= y;
  let h1 = HST.get () in
  _lemma_unchanged_node_vals_transitive h0 h' h1 (as_list h1 d);
  HST.pop_frame ()

#reset-options

#set-options "--z3rlimit 40 --max_fuel 2 --max_ifuel 1"

let dll_insert_at_tail #t d n =
  HST.push_frame ();
  let h0 = HST.get () in
  let y = DLL.dll_insert_at_tail (!*d) n in
  let h' = HST.get () in
  d *= y;
  let h1 = HST.get () in
  assert (_pred_nl_disjoint h0 (as_list h1 d)); // OBSERVE
  _lemma_unchanged_node_vals_transitive h0 h' h1 (as_list h1 d);
  HST.pop_frame ()

#reset-options

#set-options "--z3rlimit 80 --max_fuel 2 --max_ifuel 1"

let dll_insert_before #t n' d n =
  HST.push_frame ();
  let h0 = HST.get () in
  let y = DLL.dll_insert_before (!*d) n' n in
  let h' = HST.get () in
  d *= y;
  let h1 = HST.get () in
  assert (_pred_nl_disjoint h0 (as_list h1 d)); // OBSERVE
  _lemma_unchanged_node_vals_transitive h0 h' h1 (as_list h1 d);
  // assert (fp_dll h1 d `B.loc_includes` (B.loc_buffer (d@h0).DLL.lhead));
  // assert (fp_dll h1 d `B.loc_includes` (B.loc_buffer (d@h0).DLL.ltail));
  // assert (fp_dll h1 d `B.loc_includes` (B.loc_buffer n));
  _lemma_insertion_maintains_memP (as_list h0 d) (as_list h1 d) n' n n';
  // assert (n' `L.memP` as_list h1 d);
  _lemma_prev_node_in_list h0 n' d;
  FStar.Classical.arrow_to_impl #((n'@h0).DLL.blink =!= B.null)
    #((n'@h0).DLL.blink =!= B.null /\ (n'@h0).DLL.blink `L.memP` as_list h1 d)
    (fun _ ->
       _lemma_insertion_maintains_memP (as_list h0 d) (as_list h1 d) n' n (n'@h0).DLL.blink);
  // assert ((n'@h0).DLL.blink =!= B.null ==> (n'@h0).DLL.blink `L.memP` as_list h1 d);
  _lemma_node_in_list_is_included n' (as_list h1 d);
  _lemma_node_in_list_or_null_is_included (n'@h0).DLL.blink (as_list h1 d);
  // assert (fp_dll h1 d `B.loc_includes` (B.loc_buffer n'));
  // assert (fp_dll h1 d `B.loc_includes` (B.loc_buffer (n'@h0).DLL.blink));
  // assert (B.modifies (fp_dll h1 d) h0 h1);
  HST.pop_frame ()

#reset-options

#set-options "--z3rlimit 80 --max_fuel 2 --max_ifuel 1"

let dll_insert_after #t n' d n =
  HST.push_frame ();
  let h0 = HST.get () in
  let y = DLL.dll_insert_after (!*d) n' n in
  let h' = HST.get () in
  d *= y;
  let h1 = HST.get () in
  assert (_pred_nl_disjoint h0 (as_list h1 d)); // OBSERVE
  _lemma_unchanged_node_vals_transitive h0 h' h1 (as_list h1 d);
  _lemma_insertion_maintains_memP (as_list h0 d) (as_list h1 d) n' n n';
  _lemma_next_node_in_list h0 n' d;
  FStar.Classical.arrow_to_impl #((n'@h0).DLL.flink =!= B.null)
    #((n'@h0).DLL.flink =!= B.null /\ (n'@h0).DLL.flink `L.memP` as_list h1 d)
    (fun _ ->
       _lemma_insertion_maintains_memP (as_list h0 d) (as_list h1 d) n' n (n'@h0).DLL.flink);
  _lemma_node_in_list_is_included n' (as_list h1 d);
  _lemma_node_in_list_or_null_is_included (n'@h0).DLL.flink (as_list h1 d);
  // assert (B.modifies (fp_dll h1 d) h0 h1);
  HST.pop_frame ()

#reset-options

#set-options "--z3rlimit 40 --max_fuel 2 --max_ifuel 1"

let dll_remove_head #t d =
  HST.push_frame ();
  let h0 = HST.get () in
  let y = DLL.dll_remove_head (!*d) in
  let h' = HST.get () in
  d *= y;
  let h1 = HST.get () in
  _lemma_unchanged_node_vals_stays_valid0 h' h1 d;
  _lemma_unchanged_node_vals_transitive h0 h' h1 (as_list h0 d);
  HST.pop_frame ()

#reset-options

#set-options "--z3rlimit 40 --max_fuel 2 --max_ifuel 1"

let dll_remove_tail #t d =
  HST.push_frame ();
  let h0 = HST.get () in
  let y = DLL.dll_remove_tail (!*d) in
  let h' = HST.get () in
  d *= y;
  let h1 = HST.get () in

  FStar.Classical.arrow_to_impl
  #(L.length (G.reveal (d@h0).DLL.nodes) >= 2)
  #(DLL.dll_fp0 (d@h0) `B.loc_includes` B.loc_buffer ((d@h0).DLL.ltail@h0).DLL.blink)
    (fun _ ->
       DLL.extract_nodelist_conn h0 (G.reveal (d@h0).DLL.nodes) (L.length (G.reveal (d@h0).DLL.nodes) - 2);
       DLL.extract_nodelist_fp0 (G.reveal (d@h0).DLL.nodes) (L.length (G.reveal (d@h0).DLL.nodes) - 2);
       L.lemma_unsnoc_is_last (G.reveal (d@h0).DLL.nodes));

  _lemma_unchanged_node_vals_stays_valid0 h' h1 d;
  _lemma_unchanged_node_vals_transitive h0 h' h1 (as_list h0 d);
  HST.pop_frame ()

#reset-options

let dll_remove_mid #t d n =
  HST.push_frame ();
  let h0 = HST.get () in
  let y = DLL.dll_remove_node (!*d) n in
  let h' = HST.get () in
  d *= y;
  let h1 = HST.get () in
  // TODO: _lemma_unchanged_node_vals_transitive h0 h' h1 (as_list h1 d);
  HST.pop_frame ();
  admit ()

/// Automatic validity maintenance
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.

let auto_dll_remains_valid_upon_staying_unchanged h0 h1 l d =
  _lemma_nodelist_contained_in_unmodified_mem h0 h1 l (as_list h1 d);
  _lemma_nodelist_conn_in_unmodified_mem h0 h1 l (as_list h1 d)

let auto_node_remains_valid_upon_staying_unchanged h0 h1 l n = ()

let auto_node_remains_unchanged_upon_staying_unchanged_val h0 h1 n = ()

/// Automatic footprint maintenance
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.

let auto_dll_fp_upon_staying_unchanged h0 h1 l d = ()

/// Automatic value maintenance
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.

let auto_dll_as_list_staying_unchanged h0 h1 l d =()

let auto_node_val_staying_unchanged h0 h1 l n = ()

let auto_node_val_unchanged_staying_unchanged h0 h1 n =()

/// Properties of nodes inside and outside lists
///
/// These are lemmas that you shouldn't really need to refer to
/// manually. If you do, it is (likely) a bug wrt the patterns, and
/// you should ask someone who knows about how this library works to
/// look at things.

let auto_node_in_list_is_included h0 n d =
  _lemma_node_in_list_is_included n (as_list h0 d)
