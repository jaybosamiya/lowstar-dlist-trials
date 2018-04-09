module Gpointers

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = FStar.Buffer
module CN = C.Nullity

assume val gpointer_frame : (f:Monotonic.HyperHeap.rid{ST.is_eternal_region f})

type gpointer t = (p:C.Nullity.pointer t{
    B.max_length p = B.length p /\
    B.max_length p = 1 /\
    B.idx p = 0 /\
    ~(HS.is_mm (B.content p)) /\
    B.frameOf p = gpointer_frame
  })

type gpointer_or_null t = (p:C.Nullity.pointer_or_null t{
    B.max_length p = B.length p /\
    B.max_length p <= 1 /\
    B.idx p = 0 /\
    ~(HS.is_mm (B.content p)) /\
    B.frameOf p = gpointer_frame
  })

type gnull t = (p:C.Nullity.pointer_or_null t{
    B.max_length p = B.length p /\
    B.max_length p = 0 /\
    B.idx p = 0 /\
    ~(HS.is_mm (B.content p)) /\
    B.frameOf p = gpointer_frame
  })

(** Allow comparing pointers *)
val g_ptr_eq:
  #a:Type ->
  p:gpointer a ->
  q:gpointer a ->
  GTot (b:Type0{b <==> (p == q)})
let g_ptr_eq #a p q = (p == q)

(** Allow comparing pointers *)
// inline_for_extraction
assume val ptr_eq:
  #a:Type ->
  p:gpointer a ->
  q:gpointer a ->
  ST.ST bool
    (requires (fun h -> B.live h p /\ B.live h q))
    (ensures (fun h0 b h1 -> h0==h1 /\ (b <==> (g_ptr_eq p q))))

let disjoint (#t:Type) (a b: gpointer t) = B.disjoint a b

unfold let is_null (p:gpointer_or_null 't) = CN.is_null p
unfold let is_not_null (p:gpointer_or_null 't) = not (CN.is_null p)

assume val null : #t:Type -> gnull t

let test_null #t =
  let p : gpointer_or_null t = null in
  assert (is_null p)

unfold let ( := ) (a:gpointer 't) (b:'t) = B.(a.(0ul) <- b)
unfold let ( ! ) (a:gpointer 't) = B.index a 0ul

unfold let recall (#t:Type) (p: gpointer_or_null t) = B.recall p

val non_null:
  #t:Type ->
  a:gpointer_or_null t{is_not_null a} ->
  b:gpointer t
let non_null #t a = a

val lemma_non_null :
  #t:Type ->
  a:gpointer_or_null t{is_not_null a} ->
  Lemma (ensures (a == non_null a))
    [SMTPat (non_null a)]
let lemma_non_null #t a = ()

val of_non_null:
  #t:Type ->
  a:gpointer t ->
  b:gpointer_or_null t
let of_non_null #t a = a

val lemma_of_non_null:
  #t:Type ->
  a:gpointer t ->
  Lemma (ensures (is_not_null (of_non_null a)) /\ (of_non_null a == a))
let lemma_of_non_null #t a = ()

let heap = HS.mem
let contains = B.live

unfold let (@) (a:gpointer 't) (h0:heap{h0 `contains` a}) = B.get h0 a 0
unfold let (^@) (a:gpointer_or_null 't{is_not_null a}) (h0:heap{h0 `contains` (non_null a)}) = (non_null a) @ h0

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

let modifies_1 = B.modifies_1
let modifies_2 = B.modifies_2
let modifies_3 = B.modifies_3
