module DListLowInd

open FStar
open FStar.List.Tot
open Utils
open FStar.HyperStack.ST
open FStar.Ghost
open Gpointers
module Mod = FStar.Modifies
module ST = FStar.HyperStack.ST

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

let rec nodelist_contained0 (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  match nl with
  | [] -> True
  | n :: ns -> h0 `contains` n /\ nodelist_contained0 h0 ns
let rec nodelist_contained (#t:Type) (h0:heap) (nl:nodelist t) : GTot Type0 =
  nodelist_contained0 h0 nl

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
  (is_not_null d.lhead ==> is_null (d.lhead@h0).blink) /\
  (is_not_null d.ltail ==> is_null (d.ltail@h0).flink)

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

/// Extraction lemmas: these allow one to use one of the properties
/// above, which are defined inductively, to get the property at one
/// of the latter elements of the list.

let rec extract_nodelist_contained (#t:Type) (h0:heap) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (requires (nodelist_contained h0 nl))
    (ensures (h0 `contains` nl.[i])) =
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

let rec extract_nodelist_fp0 (#t:Type) (nl:nodelist t) (i:nat{i < length nl}) :
  Lemma
    (ensures (Mod.loc_includes
                (nodelist_fp0 nl)
                (Mod.loc_buffer nl.[i]))) =
  match i with
  | 0 -> ()
  | _ -> extract_nodelist_fp0 (tl nl) (i - 1)

let rec extract_fragment_fp0 (#t:Type) (f:fragment t) (i:nat{i < length f}) :
  Lemma
    (ensures (Mod.loc_includes
                (fragment_fp0 f)
                (piece_fp0 f.[i]))) =
  match i with
  | 0 -> ()
  | _ -> extract_fragment_fp0 (tl f) (i - 1)

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
    [SMTPat (Mod.loc_includes (nodelist_fp0 nl) (nodelist_fp0 (fst (unsnoc nl))))] =
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

let rec fst_unsnoc_nodelist_contained (#t:Type) (h0:heap) (nl:nodelist t) :
  Lemma
    (requires (nodelist_contained h0 nl /\ length nl > 0))
    (ensures (nodelist_contained h0 (fst (unsnoc nl)))) =
  match nl with
  | [_] -> ()
  | _ -> fst_unsnoc_nodelist_contained h0 (tl nl)

let rec fst_unsnoc_nodelist_aa (#t:Type) (nl:nodelist t) :
  Lemma
    (requires (nodelist_aa nl /\ length nl > 0))
    (ensures (nodelist_aa (fst (unsnoc nl)))) =
  match nl with
  | [_] -> ()
  | _ -> fst_unsnoc_nodelist_aa (tl nl)

let rec fst_unsnoc_nodelist_conn (#t:Type) (h0:heap) (nl:nodelist t) :
  Lemma
    (requires (nodelist_conn h0 nl /\ length nl > 0))
    (ensures (nodelist_conn h0 (fst (unsnoc nl)))) =
  match nl with
  | [_] -> ()
  | _ -> fst_unsnoc_nodelist_conn h0 (tl nl)

let fst_unsnoc_nodelist_valid (#t:Type) (h0:heap) (nl:nodelist t) :
  Lemma
    (requires (nodelist_valid h0 nl /\ length nl > 0))
    (ensures (nodelist_valid h0 (fst (unsnoc nl)))) =
  fst_unsnoc_nodelist_contained h0 nl;
  fst_unsnoc_nodelist_aa nl;
  fst_unsnoc_nodelist_conn h0 nl

(* TODO *)

/// Footprints are included, even upon breaking nodelist even further

let rec nodelist_includes_r_fp0 (#t:Type) (nl:nodelist t) (i j:nat) :
  Lemma
    (requires (i <= j /\ j < length nl))
    (ensures (
        let _, a = splitAt i nl in
        let _, b = splitAt j nl in
        Mod.loc_includes (nodelist_fp0 a) (nodelist_fp0 b)))
    (decreases (j - i)) =
  if i = j then () else (
    let _, a = splitAt i nl in lemma_splitAt i nl;
    let _, b = splitAt j nl in lemma_splitAt j nl;
    if i = j - 1 then (
      List.Pure.Properties.splitAt_assoc i 1 nl;
      // assert (tl a == b);
      ()
    ) else (
      nodelist_includes_r_fp0 nl i (j - 1);
      nodelist_includes_r_fp0 nl (j - 1) j;
      let _, c = splitAt (j - 1) nl in lemma_splitAt (j - 1) nl;
      Mod.loc_includes_trans (nodelist_fp0 a) (nodelist_fp0 c) (nodelist_fp0 b)
    )
  )

let rec nodelist_includes_l_fp0 (#t:Type) (nl:nodelist t) (i j:nat) :
  Lemma
    (requires (i <= j /\ j < length nl))
    (ensures (
       let a, _ = splitAt i nl in
       let b, _ = splitAt j nl in
       Mod.loc_includes (nodelist_fp0 b) (nodelist_fp0 a)))
    (decreases (j - i)) =
  if i = j then () else (
    let a, a' = splitAt i nl in lemma_splitAt i nl;
    let b, b' = splitAt j nl in lemma_splitAt j nl;
    if i = j - 1 then (
      List.Pure.Properties.splitAt_assoc i 1 nl;
      // assert (b == append a [hd a']);
      lemma_unsnoc_append a [hd a'];
      // assert (snd (unsnoc b) == hd a');
      // assert (fst (unsnoc b) == a);
      fst_unsnoc_nodelist_fp0 b
    ) else (
      nodelist_includes_l_fp0 nl i (j - 1);
      nodelist_includes_l_fp0 nl (j - 1) j;
      let c, c' = splitAt (j - 1) nl in lemma_splitAt (j - 1) nl;
      Mod.loc_includes_trans (nodelist_fp0 b) (nodelist_fp0 c) (nodelist_fp0 a)
    )
  )

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
    is_null (p.phead@h0).blink /\
    is_null (p.ptail@h0).flink}) :
  Tot (d:dll t{dll_valid h0 d}) =
  { lhead = p.phead ; ltail = p.ptail ; nodes = p.pnodes }

let tot_fragment_to_dll (#t:Type) (h0:heap) (f:fragment t{
    fragment_valid h0 f /\
    (length f <= 1) /\
    (length f = 1 ==> (
        (is_null ((hd f).phead@h0).blink) /\
        (is_null ((hd f).ptail@h0).flink)))
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
          (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2)))) =
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

#set-options "--z3rlimit 10"

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
    nodelist_append_fp0 nl1 nl2';
    // assert (nodelist_aa_l nl2');
    // assert (Mod.loc_includes (nodelist_fp0 nl2) (nodelist_fp0 nl2'));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl2'));
    // assert (Mod.loc_includes (nodelist_fp0 nl2) (Mod.loc_buffer n));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl1));
    // assert (loc_equiv (nodelist_fp0 (append nl1 nl2')) (Mod.loc_union (nodelist_fp0 nl1) (nodelist_fp0 nl2')));
    nodelist_append_aa_l nl1 nl2';
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 (append nl1 nl2')));
    lemma_unsnoc_append nl1 nl2;
    // assert (append nl1 nl2' == fst (unsnoc (append nl1 nl2)));
    // assert (n == snd (unsnoc (append nl1 nl2)));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 (fst (unsnoc (append nl1 nl2)))));
    ()

#reset-options

let rec nodelist_append_aa_r (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_r nl1 /\ nodelist_aa_r nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2)))
    (ensures (nodelist_aa_r (append nl1 nl2))) =
  match nl1 with
  | [] -> ()
  | _ ->
    nodelist_append_fp0 (tl nl1) nl2;
    nodelist_append_aa_r (tl nl1) nl2

let nodelist_append_aa (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa nl1 /\ nodelist_aa nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2)))
    (ensures (nodelist_aa (append nl1 nl2))) =
  nodelist_append_aa_l nl1 nl2; nodelist_append_aa_r nl1 nl2

let rec nodelist_append_conn (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_conn h0 nl1 /\ nodelist_conn h0 nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2) /\
               length nl1 > 0 /\ length nl2 > 0 /\ // For "= 0", it is trivially held
               (last nl1)@h0 |> (hd nl2) /\
               (last nl1) <| (hd nl2)@h0))
    (ensures (nodelist_conn h0 (append nl1 nl2))) =
  match nl1 with
  | [_] -> ()
  | _ -> nodelist_append_conn h0 (tl nl1) nl2

let nodelist_append_valid (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_valid h0 nl1 /\ nodelist_valid h0 nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2) /\
               length nl1 > 0 /\ length nl2 > 0 /\ // For "= 0", it is trivially held
               (last nl1)@h0 |> (hd nl2) /\
               (last nl1) <| (hd nl2)@h0))
    (ensures (nodelist_valid h0 (append nl1 nl2))) =
  nodelist_append_contained h0 nl1 nl2;
  nodelist_append_aa nl1 nl2;
  nodelist_append_conn h0 nl1 nl2

/// Properties maintained when appending fragments

let rec fragment_append_ghostly_connections (#t:Type) (f1 f2:fragment t) :
  Lemma
    (requires (fragment_ghostly_connections f1 /\ fragment_ghostly_connections f2))
    (ensures (fragment_ghostly_connections (append f1 f2))) =
  match f1 with
  | [] -> ()
  | _ -> fragment_append_ghostly_connections (tl f1) f2

let rec fragment_append_contained (#t:Type) (h0:heap) (f1 f2:fragment t) :
  Lemma
    (requires (fragment_contained h0 f1 /\ fragment_contained h0 f2))
    (ensures (fragment_contained h0 (append f1 f2))) =
  match f1 with
  | [] -> ()
  | _ -> fragment_append_contained h0 (tl f1) f2

let rec fragment_append_fp0 (#t:Type) (f1 f2:fragment t) :
  Lemma
    (ensures (
        loc_equiv
          (fragment_fp0 (append f1 f2))
          (Mod.loc_union (fragment_fp0 f1) (fragment_fp0 f2)))) =
  match f1 with
  | [] -> ()
  | p :: f1' ->
    fragment_append_fp0 f1' f2;
    loc_equiv_trans
      (Mod.loc_union (fragment_fp0 f1) (fragment_fp0 f2))
      (Mod.loc_union (piece_fp0 p) (Mod.loc_union (fragment_fp0 f1') (fragment_fp0 f2)))
      (Mod.loc_union (piece_fp0 p) (fragment_fp0 (append f1' f2)))

let rec fragment_append_aa0 (#t:Type) (f1 f2:fragment t) :
  Lemma
    (requires (fragment_aa0 f1 /\ fragment_aa0 f2 /\
               Mod.loc_disjoint (fragment_fp0 f1) (fragment_fp0 f2)))
    (ensures (fragment_aa0 (append f1 f2))) =
  match f1 with
  | [] -> ()
  | _ -> fragment_append_aa0 (tl f1) f2

let loc_includes_union_r_inv (a b c:Mod.loc) :
  Lemma
    (requires (Mod.loc_includes a (Mod.loc_union b c)))
    (ensures (Mod.loc_includes a b /\ Mod.loc_includes a c)) =
  Mod.loc_includes_trans a (Mod.loc_union b c) b;
  Mod.loc_includes_trans a (Mod.loc_union b c) c

#set-options "--z3rlimit 20"

let rec fragment_append_aa_l (#t:Type) (f1 f2:fragment t) :
  Lemma
    (requires (fragment_aa_l f1 /\ fragment_aa_l f2 /\
               Mod.loc_disjoint (fragment_fp0 f1) (fragment_fp0 f2)))
    (ensures (fragment_aa_l (append f1 f2)))
    (decreases (length f2)) =
  match f2 with
  | [] -> ()
  | _ ->
    let f2', p = unsnoc f2 in
    fragment_append_fp0 f1 f2';
    fragment_append_fp0 f2' [p];
    loc_includes_union_r_inv (fragment_fp0 f2) (fragment_fp0 f2') (fragment_fp0 [p]);
    // assert (Mod.loc_disjoint (fragment_fp0 f1) (fragment_fp0 f2'));
    fragment_append_aa_l f1 f2';
    // assert (fragment_aa_l (append f1 f2'));
    lemma_unsnoc_append f1 f2;
    // assert (append f1 f2' == fst (unsnoc (append f1 f2)));
    // assert (p == snd (unsnoc (append f1 f2)));
    extract_fragment_fp0 f2 (length f2 - 1);
    unsnoc_is_last f2;
    // assert (p == f2.[length f2 - 1]);
    // assert (Mod.loc_includes (fragment_fp0 f2) (piece_fp0 p));
    // assert (Mod.loc_disjoint (piece_fp0 p) (fragment_fp0 (append f1 f2')));
    ()

#reset-options

let rec fragment_append_aa_r (#t:Type) (f1 f2:fragment t) :
  Lemma
    (requires (fragment_aa_r f1 /\ fragment_aa_r f2 /\
               Mod.loc_disjoint (fragment_fp0 f1) (fragment_fp0 f2)))
    (ensures (fragment_aa_r (append f1 f2))) =
  match f1 with
  | [] -> ()
  | _ ->
    fragment_append_fp0 (tl f1) f2;
    fragment_append_aa_r (tl f1) f2

let rec fragment_append_aa (#t:Type) (f1 f2:fragment t) :
  Lemma
    (requires (fragment_aa f1 /\ fragment_aa f2 /\
               Mod.loc_disjoint (fragment_fp0 f1) (fragment_fp0 f2)))
    (ensures (fragment_aa (append f1 f2))) =
  fragment_append_aa0 f1 f2;
  fragment_append_aa_l f1 f2;
  fragment_append_aa_r f1 f2

let rec fragment_append_conn (#t:Type) (h0:heap) (f1 f2:fragment t) :
  Lemma
    (requires (fragment_conn h0 f1 /\ fragment_conn h0 f2))
    (ensures (fragment_conn h0 (append f1 f2))) =
  match f1 with
  | [] -> ()
  | _ -> fragment_append_conn h0 (tl f1) f2

let rec fragment_append_valid (#t:Type) (h0:heap) (f1 f2:fragment t) :
  Lemma
    (requires (fragment_valid h0 f1 /\ fragment_valid h0 f2 /\
               Mod.loc_disjoint (fragment_fp0 f1) (fragment_fp0 f2)))
    (ensures (fragment_valid h0 (append f1 f2))) =
  fragment_append_ghostly_connections f1 f2;
  fragment_append_contained h0 f1 f2;
  fragment_append_aa f1 f2;
  fragment_append_conn h0 f1 f2

/// Piece merging

let piece_merge (#t:Type) (h0:heap)
    (p1:piece t{piece_valid h0 p1})
    (p2:piece t{piece_valid h0 p2}) :
  Pure (piece t)
    (requires (let a, b = last (reveal p1.pnodes), hd (reveal p2.pnodes) in
               (a@h0 |> b) /\
               (a <| b@h0) /\
               Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p2)))
    (ensures (fun p -> piece_valid h0 p)) =
  let p = { phead = p1.phead ; ptail = p2.ptail ; pnodes = p1.pnodes ^@^ p2.pnodes } in
  lemma_last_append (reveal p1.pnodes) (reveal p2.pnodes);
  nodelist_append_valid h0 (reveal p1.pnodes) (reveal p2.pnodes);
  p

let piece_merge_fp0 (#t:Type) (h0:heap)
    (p1:piece t{piece_valid h0 p1})
    (p2:piece t{piece_valid h0 p2}) :
  Lemma
    (requires (let a, b = last (reveal p1.pnodes), hd (reveal p2.pnodes) in
               (a@h0 |> b) /\
               (a <| b@h0) /\
               Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p2)))
    (ensures (loc_equiv
                (piece_fp0 (piece_merge h0 p1 p2))
                (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)))) =
  let p = piece_merge h0 p1 p2 in
  let n1, n2, n = reveal p1.pnodes, reveal p2.pnodes, reveal p.pnodes in
  nodelist_append_fp0 n1 n2;
  // assert (loc_equiv (nodelist_fp0 n) (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2)));
  // assert (hd n1 == p1.phead);
  // assert (Mod.loc_includes (nodelist_fp0 n1) (Mod.loc_buffer p1.phead));
  // assert (Mod.loc_includes (nodelist_fp0 n) (Mod.loc_buffer p.phead));
  // assert (last n2 == p2.ptail);
  extract_nodelist_fp0 n2 (length n2 - 1);
  unsnoc_is_last n2;
  // assert (Mod.loc_includes (nodelist_fp0 n2) (Mod.loc_buffer p2.ptail));
  extract_nodelist_fp0 n (length n - 1);
  unsnoc_is_last n;
  // assert (Mod.loc_includes (nodelist_fp0 n) (Mod.loc_buffer p.ptail));
  loc_includes_union_r_inv (nodelist_fp0 n) (nodelist_fp0 n1) (nodelist_fp0 n2);
  // assert (Mod.loc_includes (nodelist_fp0 n) (nodelist_fp0 n1));
  // assert (Mod.loc_includes (nodelist_fp0 n) (nodelist_fp0 n2));
  //
  // assert (loc_equiv (nodelist_fp0 n) (piece_fp0 p));
  extract_nodelist_fp0 n1 (length n1 - 1);
  unsnoc_is_last n1;
  // assert (loc_equiv (nodelist_fp0 n1) (piece_fp0 p1));
  // assert (loc_equiv (nodelist_fp0 n2) (piece_fp0 p2));
  //
  // assert (Mod.loc_includes (nodelist_fp0 n) (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2)));
  Mod.loc_includes_trans (nodelist_fp0 n) (piece_fp0 p)
    (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2));
  Mod.loc_includes_trans (nodelist_fp0 n)
    (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2))
    (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2));
  // assert (Mod.loc_includes (piece_fp0 p) (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)));
  //
  // assert (Mod.loc_includes (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2)) (nodelist_fp0 n));
  loc_equiv_trans (nodelist_fp0 n) (piece_fp0 p)
    (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2));
  loc_equiv_trans (nodelist_fp0 n)
    (Mod.loc_union (nodelist_fp0 n1) (nodelist_fp0 n2))
    (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2))

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

let single_piece_fragment_valid (#t:Type) (h0:heap) (p:piece t) :
  Lemma
    (requires (piece_valid h0 p))
    (ensures (fragment_valid h0 [p])) = ()

#set-options "--initial_ifuel 2"

let rec tot_defragmentable_fragment_to_dll (#t:Type) (h0:heap) (f:fragment t{
    fragment_valid h0 f /\
    fragment_defragmentable h0 f /\
    (length f > 0 ==>
     (is_null ((hd f).phead@h0).blink) /\
     (is_null ((last f).ptail@h0).flink))
  }) :
  Tot (d:dll t{dll_valid h0 d})
  (decreases (length f)) =
  match f with
  | [] -> empty_list
  | [p] -> tot_piece_to_dll h0 p
  | p1 :: p2 :: ps ->
    let p = piece_merge h0 p1 p2 in
    let f' = p :: ps in
    fragment_remains_aa_l f;
    fragment_remains_aa_l (tl f);
    // assert (fragment_valid h0 ps);
    // assert (piece_aa p);
    // assert (piece_valid h0 p);
    single_piece_fragment_valid h0 p;
    // assert (fragment_aa [p]);
    // assert (fragment_aa ps);
    piece_merge_fp0 h0 p1 p2;
    // assert (loc_equiv (piece_fp0 p) (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)));
    loc_equiv_trans (fragment_fp0 [p]) (piece_fp0 p) (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2));
    // assert (Mod.loc_disjoint (piece_fp0 p2) (fragment_fp0 ps));
    // assert (Mod.loc_disjoint (piece_fp0 p1) (fragment_fp0 ps));
    assert (Mod.loc_disjoint (fragment_fp0 ps)
              (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2))); // OBSERVE
    // assert (Mod.loc_disjoint (Mod.loc_union (piece_fp0 p1) (piece_fp0 p2)) (fragment_fp0 ps));
    // assert (Mod.loc_disjoint (fragment_fp0 [p]) (fragment_fp0 ps));
    fragment_append_aa [p] ps;
    // assert (fragment_valid h0 f');
    // assert (fragment_defragmentable h0 f');
    // assert (length f' > 0);
    // assert (((hd f').phead@h0).blink == null);
    // assert (((last f').ptail@h0).flink == null);
    tot_defragmentable_fragment_to_dll h0 f'

#reset-options

/// Properties of nodelists maintained upon splitting nodelists

let rec nodelist_split_contained (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_contained h0 (append nl1 nl2)))
    (ensures (nodelist_contained h0 nl1 /\ nodelist_contained h0 nl2)) =
  match nl1 with
  | [] -> ()
  | _ :: nl1' -> nodelist_split_contained h0 nl1' nl2

let rec nodelist_split_fp0 (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_r (append nl1 nl2)))
    (ensures (Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2))) =
  match nl1 with
  | [] | [_] -> ()
  | _ ->
    match nl2 with
    | [] -> ()
    | _ ->
      // assert (length nl1 > 1);
      // assert (length nl2 > 0);
      nodelist_split_fp0 (tl nl1) nl2;
      append_length nl1 nl2;
      nodelist_includes_r_fp0 (tl (append nl1 nl2)) 0 (length nl1 - 1);
      // assert (snd (splitAt 0 (tl (append nl1 nl2))) == tl (append nl1 nl2));
      // assert (snd (splitAt (length nl1 - 1) (tl (append nl1 nl2))) == snd (splitAt (length nl1) (append nl1 nl2)));
      lemma_splitAt_append nl1 nl2;
      // assert (snd (splitAt (length nl1) (append nl1 nl2)) == nl2);
      // assert (Mod.loc_includes (nodelist_fp0 (tl (append nl1 nl2))) (nodelist_fp0 nl2));
      // assert (Mod.loc_disjoint (Mod.loc_buffer (hd nl1)) (nodelist_fp0 (tl (append nl1 nl2))));
      // assert (Mod.loc_disjoint (Mod.loc_buffer (hd nl1)) (nodelist_fp0 nl2));
      // assert (Mod.loc_disjoint (nodelist_fp0 (tl nl1)) (nodelist_fp0 nl2));
      Mod.loc_disjoint_union_r (nodelist_fp0 nl2) (Mod.loc_buffer (hd nl1)) (nodelist_fp0 (tl nl1));
      // assert (Mod.loc_disjoint (Mod.loc_union (Mod.loc_buffer (hd nl1)) (nodelist_fp0 (tl nl1))) (nodelist_fp0 nl2));
      ()

let rec nodelist_split_aa_l (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_l (append nl1 nl2)))
    (ensures (nodelist_aa_l nl1 /\ nodelist_aa_l nl2))
    (decreases (length nl2)) =
  match nl2 with
  | [] -> ()
  | _ ->
    let nl2', n = unsnoc nl2 in
    lemma_unsnoc_append nl1 nl2;
    // assert (nodelist_aa_l (append nl1 nl2));
    // assert (nodelist_aa_l (append nl1 nl2'));
    nodelist_split_aa_l nl1 nl2';
    // assert (nodelist_aa_l nl2');
    // assert (n == snd (unsnoc (append nl1 nl2)));
    // assert (n == snd (unsnoc nl2));
    nodelist_append_fp0 nl1 nl2';
    // assert (Mod.loc_includes (nodelist_fp0 (append nl1 nl2')) (nodelist_fp0 nl2'));
    // assert (Mod.loc_disjoint (Mod.loc_buffer n) (nodelist_fp0 nl2'));
    // assert (nodelist_aa_l nl2);
    ()

let rec nodelist_split_aa_r (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa_r (append nl1 nl2)))
    (ensures (nodelist_aa_r nl1 /\ nodelist_aa_r nl2)) =
  match nl1 with
  | [] -> ()
  | _ ->
    nodelist_split_aa_r (tl nl1) nl2;
    nodelist_append_fp0 (tl nl1) nl2

let nodelist_split_aa (#t:Type) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_aa (append nl1 nl2)))
    (ensures (nodelist_aa nl1 /\ nodelist_aa nl2 /\
               Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2))) =
  nodelist_split_fp0 nl1 nl2;
  nodelist_split_aa_l nl1 nl2;
  nodelist_split_aa_r nl1 nl2

let rec nodelist_split_conn (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (
        (nodelist_conn h0 (append nl1 nl2)) /\
        length nl1 > 0 /\ length nl2 > 0)) // For "= 0", it is trivially held
    (ensures (nodelist_conn h0 nl1 /\ nodelist_conn h0 nl2 /\
               (last nl1)@h0 |> (hd nl2) /\
               (last nl1) <| (hd nl2)@h0)) =
  match nl1 with
  | [_] -> ()
  | _ -> nodelist_split_conn h0 (tl nl1) nl2

let nodelist_split_valid (#t:Type) (h0:heap) (nl1 nl2:nodelist t) :
  Lemma
    (requires (nodelist_valid h0 (append nl1 nl2) /\
               length nl1 > 0 /\ length nl2 > 0)) // For "= 0", it is trivially held
    (ensures (nodelist_valid h0 nl1 /\ nodelist_valid h0 nl2 /\
              Mod.loc_disjoint (nodelist_fp0 nl1) (nodelist_fp0 nl2) /\
               (last nl1)@h0 |> (hd nl2) /\
               (last nl1) <| (hd nl2)@h0)) =
  nodelist_split_contained h0 nl1 nl2;
  nodelist_split_aa nl1 nl2;
  nodelist_split_conn h0 nl1 nl2

/// Useful lemma to convert from piece_fp0 to nodelist_fp0 and
/// vice-versa

let piece_fp0_is_nodelist_fp0 (#t:Type) (p:piece t) : Lemma
  (requires (piece_ghostly_connections p))
  (ensures
     (loc_equiv (piece_fp0 p) (nodelist_fp0 (reveal p.pnodes)))) =
  unsnoc_is_last (reveal p.pnodes)

/// Tot dll to fragment, with splitting

#set-options "--z3rlimit 20 --initial_fuel 8 --initial_ifuel 1"

let tot_dll_to_fragment_split (#t:Type) (h0:heap) (d:dll t{dll_valid h0 d})
    (n1 n2:gpointer (node t)) :
  Pure (fragment t)
    (requires (
        n1 `memP` reveal d.nodes /\
        n2 `memP` reveal d.nodes /\
        n1@h0 |> n2 /\ n1 <| n2@h0))
    (ensures (fun f -> fragment_valid h0 f /\ length f = 2)) =
  let split_nodes = elift2_p split_using d.nodes (hide n2) in
  lemma_split_using (reveal d.nodes) n2;
  let l1, l2 = (elift1 fst split_nodes), (elift1 snd split_nodes) in
  let p1 = { phead = d.lhead ; ptail = n1 ; pnodes = l1 } in
  let p2 = { phead = n2 ; ptail = d.ltail ; pnodes = l2 } in
  let f = [p1 ; p2] in
  nodelist_split_valid h0 (reveal l1) (reveal l2);
  unsnoc_is_last (reveal l1);
  unsnoc_is_last (reveal l2);
  unsnoc_is_last (reveal d.nodes);
  // assert (piece_ghostly_connections p1);
  // assert ( n2 ==$ hd (reveal l2) );
  lemma_last_append (reveal l1) (reveal l2);
  // assert ( last (reveal l2) == last (append (reveal l1) (reveal l2)) );
  // assert ( d.ltail ==$ last (reveal l2) );
  // assert (piece_ghostly_connections p2);
  // assert (fragment_ghostly_connections f);
  // assert (nodelist_contained h0 (reveal p1.pnodes));
  // assert (nodelist_contained h0 (reveal p2.pnodes));
  extract_nodelist_contained h0 (reveal l1) (length (reveal l1) - 1);
  // assert (h0 `contains` p1.ptail);
  // assert (fragment_contained h0 f);
  // assert (nodelist_aa (reveal p1.pnodes));
  // assert (nodelist_aa (reveal p2.pnodes));
  piece_fp0_is_nodelist_fp0 p1;
  piece_fp0_is_nodelist_fp0 p2;
  // assert (Mod.loc_disjoint (piece_fp0 p1) (piece_fp0 p2));
  // assert (fragment_aa f);
  // assert (nodelist_conn h0 (reveal p1.pnodes));
  // assert (nodelist_conn h0 (reveal p2.pnodes));
  // assert (fragment_conn h0 f);
  f

#reset-options

/// Creating a dll from a single node. Pure and ST forms of this.

let tot_node_to_dll (#t:Type) (h0:heap) (n:gpointer (node t)) :
  Pure (dll t)
    (requires (
        (h0 `contains` n) /\
        ((is_null (n@h0).flink)) /\
        (is_null (n@h0).blink)))
    (ensures (fun d -> dll_valid h0 d)) =
  { lhead = n ; ltail = n ; nodes = ~. n }

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

/// Creating a piece from a single node.

let tot_node_to_piece (#t:Type) (h0:heap) (n:gpointer (node t)) :
  Pure (piece t)
    (requires (
        (h0 `contains` n)))
    (ensures (fun p -> piece_valid h0 p)) =
  { phead = n ; ptail = n ; pnodes = ~. n }

/// If a dll is valid, then both the forward and backward links of
/// each of the nodes are contained in the heap

let lemma_dll_links_contained (#t:Type) (h0:heap) (d:dll t) (i:nat) :
  Lemma
    (requires (
        (dll_valid h0 d) /\
        (i < length (reveal d.nodes))))
    (ensures (
        let nodes = reveal d.nodes in
        (h0 `contains` (nodes.[i]@h0).flink) /\
        (h0 `contains` (nodes.[i]@h0).blink))) =
  let nl = reveal d.nodes in
  match nl with
  | [_] -> ()
  | _ ->
    (if i = 0 then () else extract_nodelist_conn h0 nl (i-1));
    (if i = length nl - 1 then () else extract_nodelist_conn h0 nl i);
    (if i = 0 then () else extract_nodelist_contained h0 nl (i - 1));
    (if i = length nl - 1 then () else extract_nodelist_contained h0 nl (i + 1));
    unsnoc_is_last nl

/// When something unrelated to a XYZ is changed, the XYZ itself shall
/// remain valid

let rec nodelist_remains_valid (#t:Type) (h0 h1:heap) (loc:Mod.loc) (nl:nodelist t) :
  Lemma
    (requires (
        (nodelist_valid h0 nl) /\
        (Mod.modifies loc h0 h1) /\
        (Mod.loc_disjoint loc (nodelist_fp0 nl))))
    (ensures (nodelist_valid h1 nl)) =
  match nl with
  | [] -> ()
  | _ -> nodelist_remains_valid h0 h1 loc (tl nl)

let piece_remains_valid (#t:Type) (h0 h1:heap) (loc:Mod.loc) (p:piece t) :
  Lemma
    (requires (
        (piece_valid h0 p) /\
        (Mod.modifies loc h0 h1) /\
        (Mod.loc_disjoint loc (piece_fp0 p))))
    (ensures (piece_valid h1 p)) =
  nodelist_remains_valid h0 h1 loc (reveal p.pnodes)

(* TODO *)

/// When outward facing pointers of ends of pieces are modified, they
/// still remain valid

#set-options "--z3rlimit 20"

let piece_remains_valid_b (#t:Type) (h0 h1:heap) (p:piece t) :
  Lemma
    (requires (
        (piece_valid h0 p) /\
        (Mod.modifies (Mod.loc_buffer p.phead) h0 h1) /\
        (h1 `contains` p.phead) /\
        (p.phead@h0).flink == (p.phead@h1).flink))
    (ensures (piece_valid h1 p) /\ (p.ptail@h0).flink == (p.ptail@h1).flink) =
  let nodes = reveal p.pnodes in
  if length nodes > 1 then (
    nodelist_includes_r_fp0 nodes 1 (length nodes - 1);
    unsnoc_is_last nodes;
    // assert (p.ptail == nodes.[length nodes - 1]);
    // assert (p.ptail@h0 == p.ptail@h1);
    // assert (h1 `contains` p.ptail);
    // assert (Mod.loc_disjoint (Mod.loc_buffer p.phead) (nodelist_fp0 (tl nodes)));
    nodelist_remains_valid h0 h1 (Mod.loc_buffer p.phead) (tl nodes)
  ) else ()

let piece_remains_valid_f (#t:Type) (h0 h1:heap) (p:piece t) :
  Lemma
    (requires (
        (piece_valid h0 p) /\
        (Mod.modifies (Mod.loc_buffer p.ptail) h0 h1) /\
        (h1 `contains` p.ptail) /\
        (p.ptail@h0).blink == (p.ptail@h1).blink))
    (ensures (piece_valid h1 p) /\ (p.phead@h0).blink == (p.phead@h1).blink) =
  let nodes = reveal p.pnodes in
  if length nodes > 1 then (
    fst_unsnoc_nodelist_valid h0 nodes;
    // assert (nodelist_valid h0 (fst (unsnoc nodes)));
    unsnoc_is_last nodes;
    // assert (Mod.loc_disjoint (Mod.loc_buffer p.ptail) (nodelist_fp0 (fst (unsnoc nodes))));
    nodelist_remains_valid h0 h1 (Mod.loc_buffer p.ptail) (fst (unsnoc nodes));
    // assert (nodelist_contained h1 (fst (unsnoc nodes)));
    // assert (h1 `contains` (snd (unsnoc nodes)));
    nodelist_append_contained h1 (fst (unsnoc nodes)) [snd (unsnoc nodes)];
    // assert (nodelist_contained h1 (reveal p.pnodes));
    // assert (piece_contained h1 p);
    extract_nodelist_conn h0 nodes (length nodes - 2);
    // let nl1 = fst (unsnoc nodes) in
    unsnoc_is_last (fst (unsnoc nodes));
    // assert (last nl1 == nl1.[length nl1 - 1]);
    // assert (last nl1 == nl1.[length nodes - 2]);
    index_fst_unsnoc nodes (length nodes - 2);
    // assert (last nl1 == nodes.[length nodes - 2]);
    // assert ((last (fst (unsnoc nodes)))@h0 |> (hd [snd (unsnoc nodes)]));
    // assert (Mod.loc_disjoint (nodelist_fp0 (fst (unsnoc nodes))) (Mod.loc_buffer p.ptail));
    // assert (Mod.loc_disjoint (Mod.loc_buffer (last (fst (unsnoc nodes)))) (Mod.loc_buffer p.ptail));
    // assert (Mod.modifies (Mod.loc_buffer p.ptail) h0 h1);
    extract_nodelist_contained h0 nodes (length nodes - 2);
    // assert (h0 `contains` last (fst (unsnoc nodes)));
    // assert ((last (fst (unsnoc nodes)))@h0 == (last (fst (unsnoc nodes)))@h1);
    // assert ((last (fst (unsnoc nodes)))@h1 |> (hd [snd (unsnoc nodes)]));
    // assert ((last (fst (unsnoc nodes))) <| (hd [snd (unsnoc nodes)])@h1);
    nodelist_append_conn h1 (fst (unsnoc nodes)) [snd (unsnoc nodes)];
    // assert (nodelist_conn h1 (reveal p.pnodes));
    // assert (piece_conn h1 p);
    // assert ((p.phead@h0).blink == (p.phead@h1).blink);
    ()
  ) else ()

#reset-options

/// Testing is a node is within a dll or not

let node_not_in_dll (#t:Type) (h0:heap) (n:gpointer (node t)) (d:dll t) =
  let m1 = Mod.loc_union (Mod.loc_buffer n)
      (Mod.loc_union (node_fp_b (n@h0)) (node_fp_f (n@h0))) in
  let m2 = Mod.loc_union (dll_fp0 d) (Mod.loc_union
                                        (dll_fp_f h0 d) (dll_fp_b h0 d)) in
  Mod.loc_disjoint m1 m2

/// Now for the actual ST operations that will be exposed :)

#set-options "--z3rlimit 10"

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
    y
  )

#set-options "--z3rlimit 20"

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
    assert (Mod.loc_disjoint (Mod.loc_buffer (t@h0).blink) (Mod.loc_buffer n)); // OBSERVE
    t =|> n;
    let h1 = ST.get () in
    //
    let f = tot_dll_to_fragment h0 d in
    let p = tot_node_to_piece h0 n in
    let f' = append f [p] in
    piece_remains_valid h0 h0' (Mod.loc_buffer n) (hd f);
    piece_remains_valid_f h0' h1 (hd f);
    fragment_append_valid h1 f [p];
    let y = tot_defragmentable_fragment_to_dll h1 f' in
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
  if is_null (!e).flink then (
    dll_insert_at_tail d n
  ) else (
    let e1 = (!e).blink in
    let e2 = (!e).flink in
    //
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
    assume (fragment_valid h1 f');
    assume (fragment_defragmentable h1 f');
    assert (length f' > 0);
    assume (is_null ((hd f').phead@h1).blink);
    assume (is_null ((last f').ptail@h1).flink);
    let y = tot_defragmentable_fragment_to_dll h1 f' in
    y
  )

(* TODO *)
