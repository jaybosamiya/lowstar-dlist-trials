module DListLowInd

open FStar
open Utils
open FStar.List.Tot
open FStar.HyperStack.ST
open FStar.Ghost
open Gpointers
module Mod = FStar.Modifies

/// Convenience operators

unfold let (.[]) (s:list 'a) (n:nat{n < length s}) = index s n
unfold let (~.) (#t:Type) (a:t) : Tot (erased (list t)) = hide ([a])
unfold let (^+) (#t:Type) (a:t) (b:erased (list t)) : Tot (erased (list t)) = elift2 Cons (hide a) b
unfold let (+^) (#t:Type) (a:erased (list t)) (b:t) : Tot (erased (list t)) = elift2 append a (hide [b])

/// All the data structures

unopteq
(** Node of a doubly linked list *)
type node (t:Type0) = {
  (* forward link *)
  flink: gpointer_or_null (node t);
  (* backward link *)
  blink: gpointer_or_null (node t);
  (* payload *)
  p: t;
}

abstract
type nodelist t = list (gpointer (node t))

unopteq
(** Doubly linked list head *)
type dll (t:Type0) ={
  lhead: gpointer_or_null (node t);
  ltail: gpointer_or_null (node t);
  nodes: erased (nodelist t);
}

type nonempty_dll t = (h:dll t{is_not_null h.lhead /\ is_not_null h.ltail})

unopteq abstract
(** An "almost valid" dll *)
type piece t = {
  phead: gpointer (node t);
  ptail: gpointer (node t);
  pnodes: erased (nodelist t);
}

abstract
(** An intermediate for when linked lists are being formed or destroyed *)
type fragment t = list (piece t)

/// Some useful empty initializers

(** Initialize an element of a doubly linked list *)
val empty_node: #t:Type -> payload:t -> node t
let empty_node #t payload =
  { flink = null ; blink = null ; p = payload }

(** Initialize a doubly linked list head *)
val empty_list: #t:Type -> dll t
let empty_list #t =
  { lhead = null ; ltail = null ; nodes = hide [] }

/// Ghostly connections

let dll_ghostly_connections (#t:Type) (d:dll t) : GTot Type0 =
  let nodes = reveal d.nodes in
  match length nodes with
  | 0 -> is_null d.lhead /\ is_null d.ltail
  | _ -> is_not_null d.lhead /\ is_not_null d.ltail /\
         d.lhead ==$ hd nodes /\
         d.ltail ==$ last nodes

let piece_ghostly_connections (#t:Type) (p:piece t) : GTot Type0 =
  let nodes = reveal p.pnodes in
  match length nodes with
  | 0 -> False
  | _ -> p.phead ==$ hd nodes /\
        p.ptail ==$ last nodes

/// Containment properties
///
/// WARNING: [@] and [^@] require containment to reasonably talk about
/// what they do.

let node_contained_f (#t:Type) (h0:heap) (n:node t) : GTot Type0 =
  h0 `contains` n.flink
let node_contained_b (#t:Type) (h0:heap) (n:node t) : GTot Type0 =
  h0 `contains` n.blink

let rec nodelist_contained0 (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | n :: ns -> h0 `contains` n /\ nodelist_contained0 h0 ns
let rec nodelist_contained_f (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | n :: ns -> node_contained_f h0 (n@h0) /\ nodelist_contained_f h0 ns
let rec nodelist_contained_b (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | n :: ns -> node_contained_b h0 (n@h0) /\ nodelist_contained_b h0 ns

(* dll containment is given by its ghostly connections *)

(* piece containment is given by its ghostly connections *)

/// Footprints

let node_fp_f (#t:Type) (n:node t) : GTot Mod.loc =
  Mod.loc_buffer n.flink
let node_fp_b (#t:Type) (n:node t) : GTot Mod.loc =
  Mod.loc_buffer n.blink

let rec nodelist_fp0 (#t:Type) (n:nodelist t) : GTot Mod.loc =
  match n with
  | [] -> Mod.loc_none
  | n :: ns -> Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 ns)
let rec nodelist_fp_f (#t:Type) (h0:heap) (n:nodelist t) : GTot Mod.loc =
  match n with
  | [] -> Mod.loc_none
  | n :: ns -> Mod.loc_union (Mod.loc_buffer (n@h0).flink) (nodelist_fp_f h0 ns)
let rec nodelist_fp_b (#t:Type) (h0:heap) (n:nodelist t) : GTot Mod.loc =
  match n with
  | [] -> Mod.loc_none
  | n :: ns -> Mod.loc_union (Mod.loc_buffer (n@h0).blink) (nodelist_fp_b h0 ns)

let dll_fp0 (#t:Type) (d:dll t) : GTot Mod.loc =
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union (Mod.loc_buffer d.lhead) (Mod.loc_buffer d.ltail))
    (nodelist_fp0 (reveal d.nodes))
let dll_fp_f (#t:Type) (h0:heap) (d:dll t) : GTot Mod.loc =
  let a = if is_null d.lhead then Mod.loc_none else Mod.loc_buffer (d.lhead^@h0).flink in
  let b = if is_null d.ltail then Mod.loc_none else Mod.loc_buffer (d.ltail^@h0).flink in
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union a b)
    (nodelist_fp_f h0 (reveal d.nodes))
let dll_fp_b (#t:Type) (h0:heap) (d:dll t) : GTot Mod.loc =
  let a = if is_null d.lhead then Mod.loc_none else Mod.loc_buffer (d.lhead^@h0).blink in
  let b = if is_null d.ltail then Mod.loc_none else Mod.loc_buffer (d.ltail^@h0).blink in
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union a b)
    (nodelist_fp_b h0 (reveal d.nodes))

let piece_fp0 (#t:Type) (p:piece t) : GTot Mod.loc =
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union (Mod.loc_buffer p.phead) (Mod.loc_buffer p.ptail))
    (nodelist_fp0 (reveal p.pnodes))
let piece_fp_f (#t:Type) (h0:heap) (p:piece t) : GTot Mod.loc =
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union (Mod.loc_buffer (p.phead@h0).flink) (Mod.loc_buffer (p.ptail@h0).flink))
    (nodelist_fp_f h0 (reveal p.pnodes))
let piece_fp_b (#t:Type) (h0:heap) (p:piece t) : GTot Mod.loc =
  Mod.loc_union // ghostly connections should give us this union for
                // free, but still useful to have
    (Mod.loc_union (Mod.loc_buffer (p.phead@h0).blink) (Mod.loc_buffer (p.ptail@h0).blink))
    (nodelist_fp_b h0 (reveal p.pnodes))

/// Anti aliasing properties

let node_aa (#t:Type) (n:node t) : GTot Type0 =
  Mod.loc_disjoint (node_fp_f n) (node_fp_b n)

let nodelist_aa_r (#t:Type) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | n :: ns -> Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl)
let nodelist_aa_l (#t:Type) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | _ ->
    let ns, n = unsnoc nl in
    Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl)
let nodelist_aa (#t:Type) (nl:nodelist t) : GTot Type0 =
  nodelist_aa_l nl /\ nodelist_aa_r nl

let dll_aa (#t:Type) (d:dll t) : GTot Type0 =
  nodelist_aa (reveal d.nodes)

let piece_aa (#t:Type) (p:piece t) : GTot Type0 =
  nodelist_aa (reveal p.pnodes)

/// Validity properties

(* TODO *)

/// Useful operations on nodes

logic
let node_anti_alias (#t:Type) (h0:heap) (n:node t) : GTot Type0 =
  not_aliased n.flink n.blink

let node_is_valid (#t:Type) (h0:heap) (n:gpointer (node t)) : GTot Type0 =
  h0 `contains` n /\ node_anti_alias h0 (n@h0)

logic
let ( |> ) (#t:Type) (a:node t) (b:gpointer (node t)) : GTot Type0 =
  a.flink ==$ b

logic
let ( <| ) (#t:Type) (a:gpointer (node t)) (b: node t) : GTot Type0 =
  b.blink ==$ a

irreducible
let ( =|> ) (#t:Type) (a:gpointer (node t)) (b:gpointer (node t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 b (a@h0).blink))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         node_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         b@h1 == b@h2 /\
         (a@h2) |> b)) =
  a := { !a with flink = of_non_null b }

irreducible
let ( <|= ) (#t:Type) (a:gpointer (node t)) (b:gpointer (node t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 a (b@h0).flink))
    (ensures (fun h1 _ h2 ->
         modifies_1 b h1 h2 /\
         node_is_valid h2 b /\
         a@h1 == a@h2 /\
         (b@h1).p == (b@h2).p /\
         (b@h1).flink == (b@h2).flink /\
         a <| (b@h2))) =
  b := { !b with blink = of_non_null a }

irreducible
let ( !=|> ) (#t:Type) (a:gpointer (node t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         node_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         (a@h2).flink == null)) =
  a := { !a with flink = null }

irreducible
let ( !<|= ) (#t:Type) (a:gpointer (node t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         node_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).flink == (a@h2).flink /\
         (a@h2).blink == null)) =
  a := { !a with blink = null }

let rec nodelist_valid (#t:Type) (h0:heap) (nl:nodelist t) =
  match nl with
  | [] -> True
  | a :: as ->
    node_is_valid h0 a /\
    (match as with
     | [] -> True
     | b :: bs ->
       (a@h0 |> b) /\
       (h0 `contains` b /\ a <| b@h0) /\
       nodelist_valid h0 as)

let rec nodelist_footprint (#t:Type) (h0:heap) (nl:nodelist t) : GTot Mod.loc =
  match nl with
  | [] ->
    Mod.loc_none
  | a :: as ->
    Mod.loc_union
      (Mod.loc_buffer a)
      (nodelist_footprint h0 as)

let rec nodelist_footprint_flink (#t:Type) (h0:heap) (nl:nodelist t{nodelist_valid h0 nl}) : GTot Mod.loc =
  match nl with
  | [] ->
    Mod.loc_none
  | a :: as ->
    Mod.loc_union
      (Mod.loc_buffer (a@h0).flink)
      (nodelist_footprint_flink h0 as)

let rec nodelist_footprint_blink (#t:Type) (h0:heap) (nl:nodelist t{nodelist_valid h0 nl}) : GTot Mod.loc =
  match nl with
  | [] ->
    Mod.loc_none
  | a :: as ->
    Mod.loc_union
      (Mod.loc_buffer (a@h0).blink)
      (nodelist_footprint_blink h0 as)

let rec nodelist_anti_alias_r (#t:Type) (h0:heap) (nl:nodelist t) =
  match nl with
  | [] -> True
  | a :: as ->
    h0 `contains` a /\
    Mod.loc_disjoint (Mod.loc_buffer a) (nodelist_footprint h0 as) /\
    Mod.loc_disjoint (Mod.loc_buffer (a@h0).flink) (nodelist_footprint_flink h0 as) /\
    Mod.loc_disjoint (Mod.loc_buffer (a@h0).blink) (nodelist_footprint_blink h0 as) /\
    nodelist_anti_alias_r h0 as

let rec nodelist_anti_alias_l (#t:Type) (h0:heap) (nl:nodelist t) :
  Tot Type0 (decreases (length nl)) =
  match nl with
  | [] -> True
  | _ :: _ ->
    let bs, b = unsnoc nl in
    h0 `contains` b /\
    Mod.loc_disjoint (Mod.loc_buffer b) (nodelist_footprint h0 bs) /\
    Mod.loc_disjoint (Mod.loc_buffer (b@h0).flink) (nodelist_footprint_flink h0 bs) /\
    Mod.loc_disjoint (Mod.loc_buffer (b@h0).blink) (nodelist_footprint_blink h0 bs) /\
    nodelist_anti_alias_l h0 bs
