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
  let a_0 = a in
  let b = !a in
  !a := 5;
  let a_1 = a in
  let c = !a in
  assert (a_0 == a_1);
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
  () // TODO: Look into this

// BTW, what about stuff where the type checker fails? : See below

open FStar.Ref

let foo_fail (r:option (ref int)) (h:heap) :St unit =
  /// this fails instantly on not being able to subtype on r
  // assert (Some? r ==> (Some?.v r == Some?.v r /\ sel h (Some?.v r) == sel h (Some?.v r)));
  ()

// Simply using the two phase type checker helps :)

#set-options "--use_two_phase_tc true"

let foo_pass (r:option (ref int)) (h:heap) :St unit =
  // this passes :)
  assert (Some? r ==> (Some?.v r == Some?.v r /\ sel h (Some?.v r) == sel h (Some?.v r)));
  ()
// An alternative way to do it is via a "let (r: _{phi r}) = r in ..."
// to force the type to reflect the property we need

/// Some confusing behaviour regarding refs

let t1 (a: ref (ref int)) : St unit =
  !a := 5;
  let z = !(!a) in
  // assert (z == 5); // Why does this fail?
  ()

let t2 (a: ref (ref int)) : St unit =
  let b = !a in
  let c = !a in
  assert (b == c); // passes
  b := 5;
  assert (b == c); // passes
  let z = !b in
  assert (z == 5); // passes
  let d = !a in
  // assert (b == d); // Why does this fail?
  let y = !d in
  // assert (y == 5); // Why does this fail?
  ()

/// Turns out, this happens because of possible aliasing. The following will pass:

let t1' (a: ref (ref int)) : ST unit
  (requires (fun h -> addr_of a <> addr_of (sel h a)))
  (ensures (fun _ _ _ -> True)) =
  !a := 5;
  let z = !(!a) in
  assert (z == 5);
  ()

(* Discussion on slack:

Question regarding confusing behavior regarding `ref`s:

31 replies
Jay Bosamiya [20 hours ago]
```let t1 (a: ref (ref int)) : St unit =
  !a := 5;
  let z = !(!a) in
  // assert (z == 5); // Why does this fail?
  ()

let t2 (a: ref (ref int)) : St unit =
  let b = !a in
  let c = !a in
  assert (b == c); // passes
  b := 5;
  assert (b == c); // passes
  let z = !b in
  assert (z == 5); // passes
  let d = !a in
  // assert (b == d); // Why does this fail?
  let y = !d in
  // assert (y == 5); // Why does this fail?
  ()
```


Jay Bosamiya [20 hours ago]
`t1` and `t2` do the same thing, but I have simply expanded upon different things in `t2` to try to understand why the assertion in `t1` fails.


Jay Bosamiya [20 hours ago]
The question is: the assertion in `t1` should be valid right? Or am I missing something?


nik [16 hours ago]
Hi Jay, I think you may be implicitly relying on some type-based anti-aliasing reasoning which F* does not support.


nik [16 hours ago]
This program does verify:


nik [16 hours ago]
```let t1 (a: ref (ref int)) : ST unit
  (requires (fun h -> addr_of a <> addr_of (sel h a)))
  (ensures (fun _ _ _ -> True)) =
  !a := 5;
  let z = !(!a) in
  assert (z == 5);
  ()
```


nik [16 hours ago]
If you just think in terms of the pure sel/upd operations on heaps, your original program was asking to prove something like this:


slackbot [16 hours ago] Only visible to you
:thumbsup: I will remind you about this message from @nik ("Hi Jay I...") at 9AM tomorrow.


nik [16 hours ago]
`let h' = upd h (sel h a) 5 in sel h' (sel h' a) = 5`


nik [16 hours ago]
this is only valid if `sel h' a = sel h a`

nik [16 hours ago]
which essentially requires proving that `a` and `sel h a` are not aliased (edited)

nik [16 hours ago]
one might hope that `a: ref t` and `b:ref t'` are not aliased if `t <> t'` ... but that's not necessarily true in our heap model. (Aside: it may be provable using monotonicity when `t` and `t'` are different inductive types, i.e., when they have no values in common; but that's quite a special case and an advanced usage.) (edited)


nik [16 hours ago]
so, you need the explicit anti-aliasing precondition

aseem [15 hours ago]
i was thinking an alternate to keeping anti-aliasing explicitly would be to say that both the refs are contained, and then we do have a heap lemma that says that if `t <> t'` and both refs are contained, then the refs are distinct

aseem [15 hours ago]
however, we can't prove `ref int =!= int`, i thought we should have

nik [15 hours ago]
that's because their values overlap in the representation

nik [15 hours ago]
an addr is just an int (edited)

nik [15 hours ago]
so my aside was essentially saying the if you know the values do not overlap, then using monotonicity you can recall that both references are contained, then using that you can end up showing that the addrs are distinct (edited)

aseem [15 hours ago]
right, another way to say the same(?) is that `ref` is an abstract type, so we can't prove `ref int =!= int`. on the other hand, if we define two transparent inductives, we can prove it

aseem [15 hours ago]
which makes me think, the lemma in the heap may not be that useful, it might be worth revisiting removing it's patterns, which are firing quadratically in the number of contained refs right now

nik [15 hours ago]
that would be good to remove from the context; maybe we can still get it via an explicit lemma invocation

nik [15 hours ago]
Also, wdyt about  using a fresh enumerable type for ref instead of nat, e.g., just unary numbers

nik [15 hours ago]
we might then be able to have something like `new type ref : Type0 -> Type0` in the interface, ensuring that `ref t` doesn't overlap with `int`

aseem [15 hours ago]
ref is implemented as a record, so can't we do it currently?

nik [15 hours ago]
right! should be possible

nik [14 hours ago]
ok. summarizing a side discussion with @aseem, we think we can reveal a bit more from the model, i.e., that the ref type is `new`, meaning it is a fresh inductive. That will let us prove that if `t <> s` then given `r1:ref t` and `r2:ref s` than `addr_of r1 <> addr_of r2`

nik [14 hours ago]
e.g., this will let us prove both that `ref (ref int)` is distinct from `ref int` and also that things like `ref int` and `ref nat` are not aliased



Jay Bosamiya [3 hours ago]
Ah, that makes a lot of sense :slightly_smiling_face: Thanks @nik and @aseem.


nik [2 hours ago]
While we plan to reveal more of the model to allow proving such type-based anti-aliasing, I just want to emphasize the main point of my response: implicit reasoning about anti-aliasing based on types alone is delicate. You'll have better, more predictable behavior by relying on explicit anti-aliasing invariants.


nik [2 hours ago]
e.g., even with our proposed enhancement, you will not be able to prove, say, `ref t` distinct from `ref t'` in case either `t` or `t'` are abstract. So, beware. (edited)


Jay Bosamiya [2 hours ago]
that makes sense, thanks for the clarification :slightly_smiling_face:

*)

let _ = ()

let same_addr_implies_same (#t:Type) (h0:heap) (a:ref t) (b:ref t) : unit =
  assume (h0 `contains` a);
  assert (addr_of a = addr_of b ==>
          sel h0 a == sel h0 b)
