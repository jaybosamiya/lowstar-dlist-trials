module GpointersViaRefs

open FStar.Ref

val g_ptr_eq:
  #a:Type ->
  p:ref a ->
  q:ref a ->
  GTot (b:Type0{b <==> (p == q)})
let g_ptr_eq #a p q = (p == q)

(* If two refs have the same address, and are in the heap, they are equal *)
assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma
 (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

(** Allow comparing pointers *)
// inline_for_extraction
val ptr_eq:
  #a:Type ->
  p:ref a ->
  q:ref a ->
  ST.ST bool
    (requires (fun h -> h `contains` p /\ h `contains` q))
    (ensures (fun h0 b h1 -> h0==h1 /\ (b <==> (g_ptr_eq p q))))
let ptr_eq #a p q =
  ref_extensionality (ST.get ()) p q;
  compare_addrs p q

let disjoint (#t:Type) (a b:ref t) = not (addr_of a = addr_of b)
