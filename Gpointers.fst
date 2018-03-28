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

/// The commented out part below is a _very_ bad idea, since we _may_
/// be able to prove false, by taking a ref, freeing it, and having
/// another allocate to same address, or something similar

// (* We need this for the proof *)
// assume val pointer_live_by_addr (#t:Type0) (h0:HS.mem) (p1 p2:gpointer_or_null t) :
//   Lemma ((h0 `B.live` p1 /\ B.as_addr p1 = B.as_addr p1 /\ is_not_null p2 = is_not_null p2) ==>
//          h0 `B.live` p2)
//     [SMTPat (h0 `B.live` p1); SMTPat (h0 `B.live` p2)] // TODO: Make sure this doesn't over trigger

// val stayin_alive :
// (* Whether you're a brother or whether you're a mother
//    You're stayin' alive, stayin' alive
//    Feel the city breakin' and everybody shakin'
//    I'm a-stayin' alive, stayin' alive
//    Ah, ah, ah, ah, stayin' alive, stayin' alive
//    Ah, ah, ah, ah, stayin' ali-i-i-i-ive *)
//    #t:Type ->
//    h0:HS.mem ->
//    a:gpointer_or_null t ->
//    b:gpointer_or_null t ->
//    Lemma
//      (requires (h0 `B.live` a /\ B.as_addr a = B.as_addr b /\ is_null a = is_null b))
//      (ensures (h0 `B.live` b))
// let stayin_alive #t h0 a b = ()
