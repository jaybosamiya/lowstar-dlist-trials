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
  b:gpointer t
let non_null #t a = Some?.v a

val lemma_non_null :
  #t:Type ->
  a:gpointer_or_null t{is_not_null a} ->
  Lemma (ensures (a == Some (non_null a)))
    [SMTPat (non_null a)]
let lemma_non_null #t a = ()

val of_non_null:
  #t:Type ->
  a:gpointer t ->
  b:gpointer_or_null t
let of_non_null #t a = Some a

val lemma_of_non_null:
  #t:Type ->
  a:gpointer t ->
  Lemma (ensures (is_not_null (of_non_null a)) /\ (of_non_null a == Some a))
let lemma_of_non_null #t a = ()

unfold let (@) (a:gpointer 't) (h0:heap{h0 `contains` a}) = sel h0 a
unfold let (^@) (a:gpointer_or_null 't{isSome a}) (h0:heap{h0 `contains` (non_null a)}) = (non_null a) @ h0

let (==$) (#t:Type) (a:gpointer_or_null t) (b:gpointer t) =
  is_not_null a /\
  (let (a:_{is_not_null a}) = a in // workaround for not using two phase type checker
   g_ptr_eq (non_null a) b)

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let not_aliased (#t:Type) (a:gpointer_or_null t) (b:gpointer_or_null t) : GTot Type0 =
  is_null a \/ is_null b \/
  (let (a:_{is_not_null a}) = a in // workaround for not using two phase type checker
   let (b:_{is_not_null b}) = b in
   disjoint (non_null a) (non_null b))

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let not_aliased0 (#t:Type) (a:gpointer t) (b:gpointer_or_null t) : GTot Type0 =
  is_null b \/
  (let (b:_{is_not_null b}) = b in // workaround for not using two phase type checker
   disjoint a (non_null b))

logic
let not_aliased00 (#t:Type) (a:gpointer t) (b:gpointer t) : GTot Type0 =
  disjoint a b

let modifies_1 (#t:Type) (a:gpointer t) (h0 h1:heap) =
  modifies (only a) h0 h1

let modifies_2 (#t:Type) (a b:gpointer t) (h0 h1:heap) = modifies (a ^+^ b) h0 h1

let modifies_3 (#t:Type) (a b c:gpointer t) (h0 h1:heap) = modifies (a ^++ b ^+^ c) h0 h1
