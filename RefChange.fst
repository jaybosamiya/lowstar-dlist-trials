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


// Anyways, for what I really wanted to test:

let foo (a:ref (ref int)) : St unit =
  let b = !a in
  !a := 5;
  let c = !a in
  assert (b == c \/ b =!= c); // this passes
  // assert (b == c); // this fails; shouldn't this be true?
  // assert (b =!= c); // this fails
  ()

// Looking at https://github.com/FStarLang/FStar/wiki/F*-Heap-Model
// it seems like comparing addr_of would be more useful

let bar (a:ref (ref int)) : St unit =
  let a0 = a in
  let a_deref_0 = !a in
  !a := 5;
  let a1 = a in
  let a_deref_1 = !a in
  assert (addr_of a0 == addr_of a1); // passes as expected
  // assert (addr_of a_deref_0 == addr_of a_deref_1); // fails; shouldn't this be true?
  ()
