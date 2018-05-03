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

private
type nodelist t = list (gpointer (node t))

unopteq
(** Doubly linked list head *)
type dll (t:Type0) ={
  lhead: gpointer_or_null (node t);
  ltail: gpointer_or_null (node t);
  nodes: erased (nodelist t);
}

type nonempty_dll t = (h:dll t{is_not_null h.lhead /\ is_not_null h.ltail})

unopteq private
(** An "almost valid" dll *)
type piece t = {
  phead: gpointer (node t);
  ptail: gpointer (node t);
  pnodes: erased (nodelist t);
}

private
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

let rec fragment_ghostly_connections (#t:Type) (f:fragment t) : GTot Type0 =
  match f with
  | [] -> True
  | p :: ps -> piece_ghostly_connections p /\ fragment_ghostly_connections ps

/// Containment properties
///
/// WARNING: [@] and [^@] require containment to reasonably talk about
/// what they do.

let node_contained_f (#t:Type) (h0:heap) (n:node t) : GTot Type0 =
  h0 `contains` n.flink
let node_contained_b (#t:Type) (h0:heap) (n:node t) : GTot Type0 =
  h0 `contains` n.blink
let node_contained (#t:Type) (h0:heap) (n:node t) : GTot Type0 =
  node_contained_f h0 n /\
  node_contained_b h0 n

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
let rec nodelist_contained (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  nodelist_contained0 h0 nl /\
  nodelist_contained_f h0 nl /\
  nodelist_contained_b h0 nl

let dll_contained (#t:Type) (h0:heap) (d:dll t) : GTot Type0 =
  h0 `contains` d.lhead /\
  h0 `contains` d.ltail /\
  nodelist_contained h0 (reveal d.nodes)

let piece_contained (#t:Type) (h0:heap) (p:piece t) : GTot Type0 =
  h0 `contains` p.phead /\
  h0 `contains` p.ptail /\
  nodelist_contained h0 (reveal p.pnodes)

let rec fragment_contained (#t:Type) (h0:heap) (f:fragment t) : GTot Type0 =
  match f with
  | [] -> True
  | p :: ps -> piece_contained h0 p /\ fragment_contained h0 ps

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

let rec fragment_fp0 (#t:Type) (f:fragment t) : GTot Mod.loc =
  match f with
  | [] -> Mod.loc_none
  | p :: ps -> Mod.loc_union (piece_fp0 p) (fragment_fp0 ps)
let rec fragment_fp_f (#t:Type) (h0:heap) (f:fragment t) : GTot Mod.loc =
  match f with
  | [] -> Mod.loc_none
  | p :: ps -> Mod.loc_union (piece_fp_f h0 p) (fragment_fp_f h0 ps)
let rec fragment_fp_b (#t:Type) (h0:heap) (f:fragment t) : GTot Mod.loc =
  match f with
  | [] -> Mod.loc_none
  | p :: ps -> Mod.loc_union (piece_fp_b h0 p) (fragment_fp_b h0 ps)

/// Anti aliasing properties

let node_aa (#t:Type) (n:node t) : GTot Type0 =
  Mod.loc_disjoint (node_fp_f n) (node_fp_b n)

let rec nodelist_aa_r (#t:Type) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | n :: ns ->
    Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns) /\
    nodelist_aa_r ns
let rec nodelist_aa_l (#t:Type) (nl:nodelist t) : GTot Type0 (decreases (length nl)) =
  match nl with
  | [] -> True
  | _ ->
    let ns, n = unsnoc nl in
    Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns) /\
    nodelist_aa_l ns
let nodelist_aa (#t:Type) (nl:nodelist t) : GTot Type0 =
  nodelist_aa_l nl /\ nodelist_aa_r nl

let dll_aa (#t:Type) (d:dll t) : GTot Type0 =
  nodelist_aa (reveal d.nodes)

let piece_aa (#t:Type) (p:piece t) : GTot Type0 =
  nodelist_aa (reveal p.pnodes)

let rec fragment_aa0 (#t:Type) (f:fragment t) : GTot Type0 =
  match f with
  | [] -> True
  | p :: ps -> piece_aa p /\ fragment_aa0 ps
let rec fragment_aa_r (#t:Type) (f:fragment t) : GTot Type0 =
  match f with
  | [] -> True
  | p :: ps -> Mod.loc_disjoint (piece_fp0 p) (fragment_fp0 ps) /\
             fragment_aa_r ps
let rec fragment_aa_l (#t:Type) (f:fragment t) : GTot Type0 (decreases (length f)) =
  match f with
  | [] -> True
  | _ -> let ps, p = unsnoc f in
    Mod.loc_disjoint (piece_fp0 p) (fragment_fp0 ps) /\
    fragment_aa_l ps
let fragment_aa (#t:Type) (f:fragment t) : GTot Type0 =
  fragment_aa0 f /\ fragment_aa_l f /\ fragment_aa_r f

/// Connectivity properties

let ( |> ) (#t:Type) (a:node t) (b:gpointer (node t)) : GTot Type0 =
  a.flink ==$ b

let ( <| ) (#t:Type) (a:gpointer (node t)) (b: node t) : GTot Type0 =
  b.blink ==$ a

let rec nodelist_conn (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 (decreases (length nl)) =
  match nl with
  | [] -> True
  | n1 :: rest -> match rest with
    | [] -> True
    | n2 :: ns ->
      n1@h0 |> n2 /\
      n1 <| n2@h0 /\
      nodelist_conn h0 rest

let dll_conn (#t:Type) (h0:heap) (d:dll t) : GTot Type0 =
  nodelist_conn h0 (reveal d.nodes) /\
  (is_not_null d.lhead ==> (d.lhead@h0).blink == null) /\
  (is_not_null d.ltail ==> (d.ltail@h0).flink == null)

let piece_conn (#t:Type) (h0:heap) (p:piece t) : GTot Type0 =
  nodelist_conn h0 (reveal p.pnodes)

let rec fragment_conn (#t:Type) (h0:heap) (f:fragment t) : GTot Type0 =
  match f with
  | [] -> True
  | p :: ps -> nodelist_conn h0 (reveal p.pnodes) /\ fragment_conn h0 ps

/// Validity properties
///
/// These are just a combination of
/// + Ghostly connections
/// + Containment properties
/// + Anti aliasing properties
/// + Connectivity properties

let node_valid (#t:Type) (h0:heap) (n:node t) : GTot Type0 =
  node_contained h0 n

let nodelist_valid (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  nodelist_contained h0 nl /\
  nodelist_aa nl /\
  nodelist_conn h0 nl

let dll_valid (#t:Type) (h0:heap) (d:dll t) : GTot Type0 =
  dll_ghostly_connections d /\
  dll_contained h0 d /\
  dll_aa d /\
  dll_conn h0 d

let piece_valid (#t:Type) (h0:heap) (p:piece t) : GTot Type0 =
  piece_ghostly_connections p /\
  piece_contained h0 p /\
  piece_aa p /\
  piece_conn h0 p

let fragment_valid (#t:Type) (h0:heap) (f:fragment t) : GTot Type0 =
  fragment_ghostly_connections f /\
  fragment_contained h0 f /\
  fragment_aa f /\
  fragment_conn h0 f

/// Useful operations on nodes

let ( =|> ) (#t:Type) (a:gpointer (node t)) (b:gpointer (node t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         node_contained_b h0 (a@h0) /\
         not_aliased00 a b))
    (ensures (fun h0 _ h1 ->
         modifies_1 a h0 h1 /\
         node_valid h1 (a@h1) /\
         (a@h0).p == (a@h1).p /\
         (a@h0).blink == (a@h1).blink /\
         b@h0 == b@h1 /\
         (a@h1) |> b)) =
  a := { !a with flink = of_non_null b }

let ( <|= ) (#t:Type) (a:gpointer (node t)) (b:gpointer (node t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         node_contained_f h0 (b@h0) /\
         not_aliased00 a b))
    (ensures (fun h0 _ h1 ->
         modifies_1 b h0 h1 /\
         node_valid h1 (b@h1) /\
         a@h0 == a@h1 /\
         (b@h0).p == (b@h1).p /\
         (b@h0).flink == (b@h1).flink /\
         a <| (b@h1))) =
  b := { !b with blink = of_non_null a }

let ( !=|> ) (#t:Type) (a:gpointer (node t)) : ST unit
    (requires (fun h0 -> h0 `contains` a /\ node_contained_b h0 (a@h0)))
    (ensures (fun h0 _ h1 ->
         modifies_1 a h0 h1 /\
         node_valid h1 (a@h1) /\
         (a@h0).p == (a@h1).p /\
         (a@h0).blink == (a@h1).blink /\
         (a@h1).flink == null)) =
  a := { !a with flink = null }

irreducible
let ( !<|= ) (#t:Type) (a:gpointer (node t)) : ST unit
    (requires (fun h0 -> h0 `contains` a /\ node_contained_f h0 (a@h0)))
    (ensures (fun h0 _ h1 ->
         modifies_1 a h0 h1 /\
         node_valid h1 (a@h1) /\
         (a@h0).p == (a@h1).p /\
         (a@h0).flink == (a@h1).flink /\
         (a@h1).blink == null)) =
  a := { !a with blink = null }

/// Extraction lemmas: these allow one to use one of the properties
/// above, which are defined inductively, to get the property at one
/// of the latter elements of the list.

let rec extract_nodelist_contained (#t:Type) (h0:heap) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (requires (nodelist_contained h0 nl))
    (ensures (h0 `contains` nl.[i] /\ node_contained h0 (nl.[i]@h0))) =
  match i with
  | 0 -> ()
  | _ -> extract_nodelist_contained h0 (tl nl) (i - 1)

let rec extract_fragment_contained (#t:Type) (h0:heap) (f:fragment t) (i:nat{i < length f}) :
  Lemma
    (requires (fragment_contained h0 f))
    (ensures (piece_contained h0 f.[i])) =
  match i with
  | 0 -> ()
  | _ -> extract_fragment_contained h0 (tl f) (i - 1)

let rec extract_nodelist_aa_r (#t:Type) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (requires (nodelist_aa_r nl))
    (ensures (
        let left, n, right = split3 nl i in
        Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 right))) =
  match i with
  | 0 -> ()
  | _ -> extract_nodelist_aa_r (tl nl) (i - 1)

(* TODO *)

