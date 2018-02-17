module RefChange

open FStar.Ref

let test () =
  assert (forall t (x:t) (y:t).
        ((x == y) \/ (x =!= y)) /\
        (~((x == y) /\ (x =!= y))))

let whut (a:ref int) =
  let h0 = ST.get () in
  a := 5;
  let h1 = ST.get () in
  assert (h0 == h1);
  assert (h0 =!= h1)

// Turns out, this happens due to not annotating the top level terms. Seems like lots of weird top-level specific behaviour goes on...
