module Gpointers

open C.Nullity
open FStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = FStar.Buffer
module CN = C.Nullity

type gpointer t = (p:C.Nullity.pointer t{
    B.max_length p = 1 /\
    B.idx p = 0 /\
    ~(HS.is_mm (B.content p)) /\
    ST.is_eternal_region (B.frameOf p)
  })

type gpointer_or_null t = (p:C.Nullity.pointer t{
    B.max_length p = 0 /\
    B.idx p = 0 /\
    ~(HS.is_mm (B.content p)) /\
    ST.is_eternal_region (B.frameOf p)
  })

(** Allow comparing pointers *)
// inline_for_extraction
assume val ptr_eq:
  #a:Type ->
  p:gpointer a ->
  q:gpointer a ->
  ST.ST bool
    (requires (fun h -> B.live h p /\ B.live h q))
    (ensures (fun h0 b h1 -> h0==h1 /\ (b <==> (B.as_addr p = B.as_addr q))))

(** Allow comparing pointers *)
assume val compare_addrs:
  #a:Type ->
  p:gpointer a ->
  q:gpointer a ->
  Tot (b:bool{b <==> (B.as_addr p = B.as_addr q)})

unfold let is_null (p:gpointer_or_null 't) = CN.is_null p
unfold let is_not_null (p:gpointer_or_null 't) = not (CN.is_null p)
assume val null : #t:Type -> p:gpointer_or_null t{is_null p}

unfold let ( := ) a b = a.(0ul) <- b
unfold let ( ! ) a = !* a
