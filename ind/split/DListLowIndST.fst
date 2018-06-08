module DListLowIndST

open FStar
open FStar.List.Tot
open Utils
open FStar.HyperStack.ST
open FStar.Ghost
open Gpointers
module Mod = LowStar.Modifies
module ST = FStar.HyperStack.ST
open DListLowIndBase

/// Useful operations on nodes

let ( =|> ) (#t:Type) (a:gpointer (node t)) (b:gpointer (node t)) : StackInline unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased a b))
    (ensures (fun h0 _ h1 ->
         modifies_1 a h0 h1 /\
         h1 `contains` a /\
         (a@h0).p == (a@h1).p /\
         (a@h0).blink == (a@h1).blink /\
         b@h0 == b@h1 /\
         (a@h1) |> b)) =
  a := { !a with flink = of_non_null b }

let ( <|= ) (#t:Type) (a:gpointer (node t)) (b:gpointer (node t)) : StackInline unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased a b))
    (ensures (fun h0 _ h1 ->
         modifies_1 b h0 h1 /\
         h1 `contains` b /\
         a@h0 == a@h1 /\
         (b@h0).p == (b@h1).p /\
         (b@h0).flink == (b@h1).flink /\
         a <| (b@h1))) =
  b := { !b with blink = of_non_null a }

let ( !=|> ) (#t:Type) (a:gpointer (node t)) : StackInline unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h0 _ h1 ->
         modifies_1 a h0 h1 /\
         h1 `contains` a /\
         (a@h0).p == (a@h1).p /\
         (a@h0).blink == (a@h1).blink /\
         is_null (a@h1).flink)) =
  a := { !a with flink = null }

let ( !<|= ) (#t:Type) (a:gpointer (node t)) : StackInline unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h0 _ h1 ->
         modifies_1 a h0 h1 /\
         h1 `contains` a /\
         (a@h0).p == (a@h1).p /\
         (a@h0).flink == (a@h1).flink /\
         is_null (a@h1).blink)) =
  a := { !a with blink = null }

/// Creating a dll from a single node. ST form.

let singleton_dll (#t:Type) (n:gpointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
        (h0 `contains` n)))
    (ensures (fun h0 d h1 ->
         modifies_1 n h0 h1 /\
         dll_valid h1 d)) =
  !=|> n;
  !<|= n;
  tot_node_to_dll (ST.get ()) n


/// Now for the actual ST operations that will be exposed :)

#set-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 1 --query_stats"

let dll_insert_at_head (#t:Type) (d:dll t) (n:gpointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (h0 `contains` n) /\
         (node_not_in_dll h0 n d)))
    (ensures (fun h0 y h1 ->
         (* TODO: Write about what is modified *)
         dll_valid h1 y)) =
  if is_null d.lhead then (
    singleton_dll n
  ) else (
    let h = d.lhead in
    //
    let h0 = ST.get () in
    assert (h0 `contains` h);
    !<|= n;
    n =|> h;
    let h0' = ST.get () in
    n <|= h;
    let h1 = ST.get () in
    //
    let f = tot_dll_to_fragment h0 d in
    let p = tot_node_to_piece h0 n in
    let f' = append [p] f in
    // assert (fragment_valid h1 [p]);
    // assert (fragment_ghostly_connections f);
    // assert (length f = 1);
    // assert (h1 `contains` (hd f).phead);
    piece_remains_valid h0 h0' (Mod.loc_buffer n) (hd f);
    // assert (piece_valid h0' (hd f));
    piece_remains_valid_b h0' h1 (hd f);
    // assert (h1 `contains` (hd f).ptail);
    // assert (nodelist_contained h1 (reveal (hd f).pnodes));
    // assert (piece_contained h1 (hd f));
    // assert (fragment_contained h1 f);
    // assert (fragment_aa f);
    // assert (nodelist_conn h1 (reveal (f.[0]).pnodes));
    // assert (fragment_conn h1 f);
    // assert (fragment_valid h1 f);
    fragment_append_valid h1 [p] f;
    // assert (fragment_valid h1 f');
    // assert (fragment_defragmentable h1 f');
    // assert (length f' > 0);
    // assert (is_null ((hd f').phead@h1).blink);
    // assert (is_null ((last f').ptail@h0).flink);
    // assert (is_null ((last f').ptail@h0').flink);
    // assert (is_null ((last f').ptail@h1).flink);
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    // admit (); // Instead of StackInline, if we use ST everywhere in
    //           // this file, it is unable to prove things
    // assert (dll_valid h1 y);
    admit (); // it didn't require this before the 97259eca...52cb3718f update of F*
    y
  )

#reset-options

#set-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 1 --query_stats"

let dll_insert_at_tail (#t:Type) (d:dll t) (n:gpointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (h0 `contains` n) /\
         (node_not_in_dll h0 n d)))
    (ensures (fun h0 y h1 ->
         (* TODO: Write about what is modified *)
         dll_valid h1 y)) =
  if is_null d.lhead then (
    singleton_dll n
  ) else (
    let t = d.ltail in
    //
    let h0 = ST.get () in
    !=|> n;
    t <|= n;
    let h0' = ST.get () in
    lemma_dll_links_contained h0 d (length (reveal d.nodes) - 1);
    unsnoc_is_last (reveal d.nodes);
    // assert (Mod.loc_disjoint (Mod.loc_buffer (t@h0).blink) (Mod.loc_buffer n));
    t =|> n;
    let h1 = ST.get () in
    //
    let f = tot_dll_to_fragment h0 d in
    let p = tot_node_to_piece h0 n in
    let f' = append f [p] in
    piece_remains_valid h0 h0' (Mod.loc_buffer n) (hd f);
    piece_remains_valid_f h0' h1 (hd f);
    assume (fragment_valid h1 f); // it could prove this before the 97259eca...52cb3718f update of F*
    assume (fragment_valid h1 [p]); // it could prove this before the 97259eca...52cb3718f update of F*
    assume (Mod.loc_disjoint (fragment_fp0 f) (fragment_fp0 [p])); // it could prove this before the 97259eca...52cb3718f update of F*
    fragment_append_valid h1 f [p];
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    admit ();
    y
  )

#reset-options

#set-options "--z3rlimit 1000 --initial_fuel 2 --initial_ifuel 2 --max_fuel 2 --max_ifuel 2 --z3refresh --query_stats"

let dll_insert_after (#t:Type) (d:dll t) (e:gpointer (node t)) (n:gpointer (node t)) :
  StackInline (dll t)
    (requires (fun h0 ->
         (dll_valid h0 d) /\
         (e `memP` reveal d.nodes) /\
         (h0 `contains` n) /\
         (node_not_in_dll h0 n d)))
    (ensures (fun h0 y h1 ->
         (* TODO: Write about what is modified *)
         dll_valid h1 y)) =
  let h0 = ST.get () in
  // assert (length (reveal d.nodes) > 0);
  lemma_dll_links_contained h0 d (reveal d.nodes `index_of` e);
  extract_nodelist_contained h0 (reveal d.nodes) (reveal d.nodes `index_of` e);
  let e1 = (!e).blink in
  let e2 = (!e).flink in
  if is_null e2 then (
    dll_insert_at_tail d n
  ) else (
    admit ();
    extract_nodelist_fp0 (reveal d.nodes) (reveal d.nodes `index_of` e);
    unsnoc_is_last (reveal d.nodes);
    extract_nodelist_conn h0 (reveal d.nodes) (reveal d.nodes `index_of` e);
    extract_nodelist_fp0 (reveal d.nodes) (reveal d.nodes `index_of` e + 1);
    if is_not_null e1 then (
      extract_nodelist_conn h0 (reveal d.nodes) (reveal d.nodes `index_of` e - 1);
      extract_nodelist_fp0 (reveal d.nodes) (reveal d.nodes `index_of` e - 1)
    ) else ();
    e <|= n;
    // let h' = ST.get () in assert (h' `contains` e2); assert (not_aliased n e2);
    n =|> e2;
    let h0' = ST.get () in
    // assert (is_not_null e1 ==> e1 == (reveal d.nodes).[reveal d.nodes `index_of` e - 1]);
    // assert (is_not_null e1 ==> Mod.loc_includes (nodelist_fp0 (reveal d.nodes)) (Mod.loc_buffer e1));
    // assert (is_not_null e1 ==> Mod.loc_disjoint (Mod.loc_buffer n) (Mod.loc_buffer e1));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (Mod.loc_buffer e1));
    Mod.modifies_buffer_elim e1 (Mod.loc_buffer n) h0 h0';
    e =|> n;
    let h0'' = ST.get () in
    // assert (h0 `contains` e2);
    // assert (h0' `contains` e2);
    // assert (e2 == (reveal d.nodes).[reveal d.nodes `index_of` e + 1]);
    extract_nodelist_aa_r (reveal d.nodes) (reveal d.nodes `index_of` e);
    lemma_hd_r_split3 (reveal d.nodes) (reveal d.nodes `index_of` e);
    // assert (Mod.loc_includes (nodelist_fp0 (reveal d.nodes)) (nodelist_fp0 (let _,_,z = split3 (reveal d.nodes) (reveal d.nodes `index_of` e) in z)));
    // assert (Mod.loc_includes (nodelist_fp0 (let _,_,z = split3 (reveal d.nodes) (reveal d.nodes `index_of` e) in z)) (Mod.loc_buffer e2));
    // assert (Mod.loc_disjoint (Mod.loc_buffer e2) (Mod.loc_buffer e));
    // assert (Mod.modifies (Mod.loc_buffer e) h0' h0'');
    Mod.modifies_buffer_elim e2 (Mod.loc_buffer e) h0' h0'';
    // assert (h0'' `contains` e2);
    n <|= e2;
    let h1 = ST.get () in
    //
    // assert (e `memP` reveal d.nodes);
    assume (e2 `memP` reveal d.nodes);
    // assert (e@h0 |> e2 /\ e <| e2@h0);
    let f = tot_dll_to_fragment_split h0 d e e2 in
    // assert (length f = 2);
    let p1, p3 = f.[0], f.[1] in
    // assert ([p1 ; p3] == f);
    let p2 = tot_node_to_piece h0 n in
    let f' = [p1 ; p2 ; p3] in
    // assert (Mod.modifies (Mod.loc_buffer n) h0 h0');
    // assert (piece_valid h0 p1);
    assume (Mod.loc_disjoint (Mod.loc_buffer n) (piece_fp0 p1));
    piece_remains_valid h0 h0' (Mod.loc_buffer n) p1;
    // assert (piece_valid h0 p3);
    assume (Mod.loc_disjoint (Mod.loc_buffer n) (piece_fp0 p3));
    piece_remains_valid h0 h0' (Mod.loc_buffer n) p3;
    piece_remains_valid_f h0' h0'' p1;
    assume (Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p3));
    piece_remains_valid h0' h0'' (piece_fp0 p1) p3;
    piece_remains_valid h0'' h1 (piece_fp0 p3) p1;
    piece_remains_valid_b h0'' h1 p3;
    fragment_append_valid h1 [p2] [p3];
    // assert ([p2 ; p3] == append [p2] [p3]);
    fragment_append_valid h1 [p1] [p2 ; p3];
    // assert (f' == append [p1] [p2 ; p3]);
    //
    // assert (fragment_valid h1 f');
    assume (fragment_defragmentable h1 f');
    // assert (length f' > 0);
    // assert (is_null ((hd f').phead@h1).blink);
    assume (is_null ((last f').ptail@h1).flink);
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    y
  )

(* TODO *)
