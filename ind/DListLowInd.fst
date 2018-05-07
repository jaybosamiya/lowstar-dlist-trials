module DListLowInd

open FStar
open FStar.List.Tot
open Utils
open FStar.HyperStack.ST
open FStar.Ghost
open Gpointers
module Mod = FStar.Modifies

/// Convenience operators

unfold let (.[]) (s:list 'a) (n:nat{n < length s}) = index s n
unfold let (~.) (#t:Type) (a:t) : Tot (erased (list t)) = hide ([a])
unfold let (^+) (#t:Type) (a:t) (b:erased (list t)) : Tot (erased (list t)) = elift2 Cons (hide a) b
unfold let (+^) (#t:Type) (a:erased (list t)) (b:t) : Tot (erased (list t)) = elift2 append a (hide [b])
unfold let (^@^) (#t:Type) (a:erased (list t)) (b:erased (list t)) : Tot (erased (list t)) = elift2 append a b

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

let rec extract_nodelist_aa_l (#t:Type) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (requires (nodelist_aa_l nl))
    (ensures (
        let left, n, right = split3 nl i in
        Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 left)))
    (decreases (length nl)) =
  if i = length nl - 1 then () else (
    let a, b = unsnoc nl in
    let left, n, right = split3 nl i in
    lemma_unsnoc_split3 nl i;
    // assert (append (left) (n :: (fst (unsnoc right))) == a);
    extract_nodelist_aa_l a i;
    lemma_split3_unsnoc nl i
  )

let rec extract_fragment_aa0 (#t:Type) (f:fragment t) (i:nat{i < length f}) :
  Lemma
    (requires (fragment_aa0 f))
    (ensures (piece_aa f.[i])) =
  match i with
  | 0 -> ()
  | _ -> extract_fragment_aa0 (tl f) (i - 1)

let rec extract_fragment_aa_r (#t:Type) (f:fragment t) (i:nat{i < length f}) :
  Lemma
    (requires (fragment_aa_r f))
    (ensures (
        let left, p, right = split3 f i in
        Mod.loc_disjoint (piece_fp0 p) (fragment_fp0 right))) =
  match i with
  | 0 -> ()
  | _ -> extract_fragment_aa_r (tl f) (i - 1)

let rec extract_fragment_aa_l (#t:Type) (f:fragment t) (i:nat{i < length f}) :
  Lemma
    (requires (fragment_aa_l f))
    (ensures (
        let left, p, right = split3 f i in
        Mod.loc_disjoint (piece_fp0 p) (fragment_fp0 left)))
    (decreases (length f)) =
  if i = length f - 1 then () else (
    let a, b = unsnoc f in
    let left, p, right = split3 f i in
    lemma_unsnoc_split3 f i;
    // assert (append (left) (n :: (fst (unsnoc right))) == a);
    extract_fragment_aa_l a i;
    lemma_split3_unsnoc f i
  )

let rec extract_nodelist_conn (#t:Type) (h0:heap) (nl:nodelist t) (i:nat{i < length nl - 1}) :
  Lemma
    (requires (nodelist_conn h0 nl))
    (ensures (
        (nl.[i]@h0 |> nl.[i+1]) /\
        (nl.[i] <| nl.[i+1]@h0)))
    (decreases (length nl)) =
  match i with
  | 0 -> ()
  | _ -> extract_nodelist_conn h0 (tl nl) (i - 1)

let rec extract_fragment_conn (#t:Type) (h0:heap) (f:fragment t) (i:nat{i < length f}) :
  Lemma
    (requires (fragment_conn h0 f))
    (ensures (nodelist_conn h0 (reveal (f.[i]).pnodes))) =
  match i with
  | 0 -> ()
  | _ -> extract_fragment_conn h0 (tl f) (i - 1)

/// Validity is maintained upon breaking the lists, via (hd :: tl)

let rec nodelist_remains_aa_l (#t:Type) (nl:nodelist t) :
  Lemma
    (requires (nodelist_aa_l nl /\ length nl > 0))
    (ensures (nodelist_aa_l (tl nl)))
    (decreases (length nl))
    [SMTPat (nodelist_aa_l (tl nl))] =
  match nl with
  | [n] -> ()
  | _ ->
    let ns, n = unsnoc nl in
    let ns', n' = unsnoc (tl nl) in
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns));
    // assert (n' == n);
    // assert (ns' == tl ns);
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 ns'));
    nodelist_remains_aa_l ns

let rec fragment_remains_aa_l (#t:Type) (f:fragment t) :
  Lemma
    (requires (fragment_aa_l f /\ length f > 0))
    (ensures (fragment_aa_l (tl f)))
    (decreases (length f))
    [SMTPat (fragment_aa_l (tl f))] =
  match f with
  | [p] -> ()
  | _ ->
    let ps, p = unsnoc f in
    let ps', p' = unsnoc (tl f) in
    // assert (Mod.loc_disjoint (piece_fp0 p) (fragment_fp0 ps));
    // assert (p' == p);
    // assert (ps' == tl ps);
    // assert (Mod.loc_disjoint (piece_fp0 p) (fragment_fp0 ps'));
    fragment_remains_aa_l ps

(* Rest of the validity predicates are held trivially due to their
   direction of definition *)

/// Properties maintained upon breaking the list, via unsnoc

let rec fst_unsnoc_nodelist_fp0 (#t:Type) (nl:nodelist t) :
  Lemma
    (requires (length nl > 0))
    (ensures (Mod.loc_includes (nodelist_fp0 nl) (nodelist_fp0 (fst (unsnoc nl)))))
    [SMTPat (nodelist_fp0 (fst (unsnoc nl)))] =
  match nl with
  | [_] -> ()
  | n :: ns -> fst_unsnoc_nodelist_fp0 ns

let rec snd_unsnoc_nodelist_fp0 (#t:Type) (nl:nodelist t) :
  Lemma
    (requires (length nl > 0))
    (ensures (Mod.loc_includes (nodelist_fp0 nl) (Mod.loc_buffer (snd (unsnoc nl)))))
    [SMTPat (Mod.loc_includes (nodelist_fp0 nl) (Mod.loc_buffer (snd (unsnoc nl))))] =
  match nl with
  | [_] -> ()
  | n :: ns -> snd_unsnoc_nodelist_fp0 ns

(* TODO *)

/// Total conversions between fragments, pieces, and dlls

let tot_dll_to_piece (#t:Type) (h0:heap) (d:nonempty_dll t{dll_valid h0 d}) :
  Tot (p:piece t{piece_valid h0 p}) =
  { phead = d.lhead ; ptail = d.ltail ; pnodes = d.nodes }

let tot_dll_to_fragment (#t:Type) (h0:heap) (d:dll t{dll_valid h0 d}) :
  Tot (f:fragment t{fragment_valid h0 f}) =
  if is_not_null d.lhead && is_not_null d.ltail then [tot_dll_to_piece h0 d] else []

let tot_piece_to_dll (#t:Type) (h0:heap) (p:piece t{
    piece_valid h0 p /\
    (p.phead@h0).blink == null /\
    (p.ptail@h0).flink == null}) :
  Tot (d:dll t{dll_valid h0 d}) =
  { lhead = p.phead ; ltail = p.ptail ; nodes = p.pnodes }

let tot_fragment_to_dll (#t:Type) (h0:heap) (f:fragment t{
    fragment_valid h0 f /\
    (length f <= 1) /\
    (length f = 1 ==> (
        (((hd f).phead@h0).blink == null) /\
        (((hd f).ptail@h0).flink == null)))
  }) :
  Tot (d:dll t{dll_valid h0 d}) =
  match f with
  | [] -> empty_list
  | [p] -> tot_piece_to_dll h0 p

(* The conversions piece<->fragment are trivial *)

/// Properties maintained when appending nodelists

let rec nodelist_append_contained (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_contained h0 nl1 /\ nodelist_contained h0 nl2))
    (ensures (nodelist_contained h0 (append nl1 nl2))) =
  match nl1 with
  | [] -> ()
  | _ :: nl1' -> nodelist_append_contained h0 nl1' nl2

unfold let loc_equiv (a b:Mod.loc) = Mod.loc_includes a b /\ Mod.loc_includes b a

let loc_equiv_trans (a b c:Mod.loc) :
  Lemma
    (requires (loc_equiv a b /\ loc_equiv b c))
    (ensures (loc_equiv a c))
    [SMTPat (loc_equiv a b);
     SMTPat (loc_equiv b c);
     SMTPat (loc_equiv a c)] =
  Mod.loc_includes_trans a b c;
  Mod.loc_includes_trans c b a

let rec nodelist_append_fp0 (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (ensures (
        loc_equiv
          (nodelist_fp0 (append nl1 nl2))
          (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2))))
    [SMTPat (nodelist_fp0 (append nl1 nl2))] =
  match nl1 with
  | [] -> ()
  | n :: nl1' ->
    nodelist_append_fp0 nl1' nl2;
    // assert (loc_equiv
    //           (nodelist_fp0 (append nl1' nl2))
    //           (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2)));
    // assert (loc_equiv
    //          (nodelist_fp0 nl1)
    //          (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 nl1')));
    // assert (loc_equiv
    //           (Mod.loc_union (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 nl1')) (nodelist_fp0 nl2))
    //           (Mod.loc_union (Mod.loc_buffer n) (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2))));
    // assert (loc_equiv
    //           (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2))
    //           (Mod.loc_union (Mod.loc_buffer n) (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2))));
    // assert (loc_equiv
    //           (Mod.loc_union (Mod.loc_buffer n) (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2)))
    //           (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 (append nl1' nl2))));
    loc_equiv_trans
      (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2))
      (Mod.loc_union (Mod.loc_buffer n) (Mod.loc_union (nodelist_fp0 nl1') (nodelist_fp0 nl2)))
      (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 (append nl1' nl2)));
    // assert (loc_equiv
    //           (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2))
    //           (Mod.loc_union (Mod.loc_buffer n) (nodelist_fp0 (append nl1' nl2))));
    ()

let rec nodelist_append_aa_l (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_l nl1 /\ nodelist_aa_l nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2)))
    (ensures (nodelist_aa_l (append nl1 nl2)))
    (decreases (length nl2)) =
  match nl2 with
  | [] -> ()
  | _ ->
    let nl2', n = unsnoc nl2 in
    // assert (nodelist_aa_l nl2');
    // assert (Mod.loc_includes (nodelist_fp0 nl2) (nodelist_fp0 nl2'));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl2'));
    // assert (Mod.loc_includes (nodelist_fp0 nl2) (Mod.loc_buffer n));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl1));
    assume (nodelist_fp0 (append nl1 nl2') == Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2'));
    nodelist_append_aa_l nl1 nl2';
    assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 (append nl1 nl2')));
    admit ();
    ()

(* TODO *)

/// Piece merging

let piece_merge (#t:Type) (h0:heap)
    (p1:piece t{piece_valid h0 p1})
    (p2:piece t{piece_valid h0 p2}) :
  Pure (p:piece t{piece_valid h0 p})
    (requires (let a, b = last (reveal p1.pnodes), hd (reveal p2.pnodes) in
               (a@h0 |> b) /\
               (a <| b@h0)))
    (ensures (fun _ -> True)) =
  let p = { phead = p1.phead ; ptail = p2.ptail ; pnodes = p1.pnodes ^@^ p2.pnodes } in
  nodelist_append_contained h0 (reveal p1.pnodes) (reveal p2.pnodes);
  assume (nodelist_aa_l (reveal p.pnodes));
  assume (nodelist_aa_r (reveal p.pnodes));
  assume (piece_conn h0 p);
  p

(* TODO *)

/// Fragment merging to a dll

let rec fragment_defragmentable (#t:Type) (h0:heap) (f:fragment t{fragment_valid h0 f}) :
  GTot Type0 (decreases (length f)) =
  match f with
  | [] -> True
  | p1 :: rest -> match rest with
    | [] -> True
    | p2 :: ps ->
      let a, b = last (reveal p1.pnodes), hd (reveal p2.pnodes) in
      (a@h0 |> b) /\
      (a <| b@h0) /\
      (assert (rest == tl f); // OBSERVE
         fragment_defragmentable h0 rest)

let tot_defragmentable_fragment_to_dll (#t:Type) (h0:heap) (f:fragment t{
    fragment_defragmentable h0 f
  }) :
  Tot (d:dll t{dll_valid h0 d}) =
  match f with
  | [] -> empty_list
  | [p] -> tot_piece_to_dll h0 p
  | _ ->
    let p1, p2 = hd f, last f in
    admit ();
    empty_list
