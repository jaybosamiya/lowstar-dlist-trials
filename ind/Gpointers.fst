module Gpointers

open LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module BO = LowStar.BufferOps
module Mod = LowStar.Modifies

let null #t : pointer_or_null t = B.null #t

assume val is_null (p:pointer_or_null 't) : Tot (b:bool{b <==> p == null})
let is_not_null (p:pointer_or_null 't) = not (is_null p)

let lemma_is_null (p:pointer_or_null 't) :
  Lemma
    (ensures (is_null p <==> B.g_is_null p))
    [SMTPat (is_null p)]
    = B.null_unique p
