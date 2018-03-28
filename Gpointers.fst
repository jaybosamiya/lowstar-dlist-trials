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
// inline_for_extraction
assume val ptr_eq:
  #a:Type ->
  p:gpointer a ->
  q:gpointer a ->
  ST.ST bool
    (requires (fun h -> B.live h p /\ B.live h q))
    (ensures (fun h0 b h1 -> h0==h1 /\ (b <==> (p == q))))

(** Allow comparing pointers *)
assume val compare_addrs:
  #a:Type ->
  p:gpointer a ->
  q:gpointer a ->
  GTot (b:bool{b <==> (p == q)})

unfold let is_null (p:gpointer_or_null 't) = CN.is_null p
unfold let is_not_null (p:gpointer_or_null 't) = not (CN.is_null p)

assume val null : #t:Type -> gnull t

let test_null #t =
  let p : gpointer_or_null t = null in
  assert (is_null p)

open C.Nullity
open FStar.Buffer

unfold let ( := ) (a:gpointer 't) (b:'t) = a.(0ul) <- b
unfold let ( ! ) (a:gpointer 't) = !* a

unfold let recall (#t:Type) (p: gpointer_or_null t) = recall p
