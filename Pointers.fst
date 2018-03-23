module Pointers

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = FStar.Buffer
module CN = C.Nullity

type pointer t = (p:C.Nullity.pointer t{
    B.max_length p = 1 /\
    B.idx p = 0 /\
    ~(HS.is_mm (B.content p)) /\
    ST.is_eternal_region (B.frameOf p)
  })

type pointer_or_null t = (p:C.Nullity.pointer t{
    B.max_length p = 0 /\
    B.idx p = 0 /\
    ~(HS.is_mm (B.content p)) /\
    ST.is_eternal_region (B.frameOf p)
  })

(** Allow comparing pointers *)
// inline_for_extraction
assume val ptr_eq:
  #a:Type ->
  p:pointer a ->
  q:pointer a ->
  ST.ST bool
    (requires (fun h -> B.live h p /\ B.live h q))
    (ensures (fun h0 b h1 -> h0==h1 /\ (b <==> (B.as_addr p = B.as_addr q))))

(** Allow comparing pointers *)
assume val compare_addrs:
  #a:Type ->
  p:pointer a ->
  q:pointer a ->
  Tot (b:bool{b <==> (B.as_addr p = B.as_addr q)})

unfold let is_null (p:pointer_or_null 't) = CN.is_null p
unfold let is_not_null (p:pointer_or_null 't) = not (CN.is_null p)
assume val null : #t:Type -> p:pointer_or_null t{is_null p}

open CN
open B

unfold let ( := ) a b = a.(0ul) <- b
unfold let ( ! ) a = !* a
