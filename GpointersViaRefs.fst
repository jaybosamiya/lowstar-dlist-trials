module GpointersViaRefs

open FStar.Ref
open FStar.Option

type gpointer t = ref t
type gpointer_or_null t = option (ref t)
type gnull t = (p:option (ref t){isNone p})

val g_ptr_eq:
  #a:Type ->
  p:gpointer a ->
  q:gpointer a ->
  GTot (b:Type0{b <==> (p == q)})
let g_ptr_eq #a p q = (p == q)

(* If two refs have the same address, and are in the heap, they are equal *)
assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma
 (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

(** Allow comparing pointers *)
// inline_for_extraction
val ptr_eq:
  #a:Type ->
  p:gpointer a ->
  q:gpointer a ->
  ST.ST bool
    (requires (fun h -> h `contains` p /\ h `contains` q))
    (ensures (fun h0 b h1 -> h0==h1 /\ (b <==> (g_ptr_eq p q))))
let ptr_eq #a p q =
  ref_extensionality (ST.get ()) p q;
  compare_addrs p q

let disjoint (#t:Type) (a b:ref t) = not (addr_of a = addr_of b)

unfold let is_null (p:gpointer_or_null 't) = isNone p
unfold let is_not_null (p:gpointer_or_null 't) = not (isNone p)

let null = None

let test_null #t =
  let p : gpointer_or_null t = null in
  assert (is_null p)

unfold let ( := ) (a:gpointer 't) (b:'t) = a := b
unfold let ( ! ) (a:gpointer 't) = !a

unfold let recall (#t:Type) (p: gpointer t) = recall p

val non_null:
  #t:Type ->
  a:gpointer_or_null t{is_not_null a} ->
  b:gpointer t{a == Some b}
let non_null #t a = Some?.v a

unfold let (@) (a:gpointer 't) (h0:heap{h0 `contains` a}) = sel h0 a
unfold let (^@) (a:gpointer_or_null 't{isSome a}) (h0:heap{h0 `contains` (non_null a)}) = (non_null a) @ h0
