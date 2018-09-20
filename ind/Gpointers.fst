module Gpointers

open LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module BO = LowStar.BufferOps
module Mod = LowStar.Modifies

let disjoint (#t:Type) (a b: pointer t) = B.as_addr a <> B.as_addr b

let null #t : pointer_or_null t = B.null #t

assume val is_null (p:pointer_or_null 't) : Tot (b:bool{b <==> p == null})
let is_not_null (p:pointer_or_null 't) = not (is_null p)

let lemma_is_null (p:pointer_or_null 't) :
  Lemma
    (ensures (is_null p <==> B.g_is_null p))
    [SMTPat (is_null p)]
    = B.null_unique p

let test_null #t =
  let p : pointer_or_null t = null in
  assert (is_null p)

val non_null:
  #t:Type ->
  a:pointer_or_null t{is_not_null a} ->
  b:pointer t
let non_null #t a = a

val lemma_non_null :
  #t:Type ->
  a:pointer_or_null t{is_not_null a} ->
  Lemma (ensures (a == non_null a))
    [SMTPat (non_null a)]
let lemma_non_null #t a = ()

val of_non_null:
  #t:Type ->
  a:pointer t ->
  b:pointer_or_null t
let of_non_null #t a = a
