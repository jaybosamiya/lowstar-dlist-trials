# LowStar DList Trials

Work In Progress!

---

In this repository, I have been working on a LowStar (see
[F\*](https://fstar-lang.org/) and
[KreMLin](https://github.com/FStarLang/kremlin/)) implementation of a
doubly linked list based container library.

While the code for a doubly linked list is quite simple to write,
coming up with an efficient implementation _with_ a proof of
correctness is significantly more challenging, as evidenced by the
commit history of this repository.

At the moment, the code supports storing doubly linked lists of any
generic type, along with insertion and deletions from anywhere in the
list. Each stateful operation is currently implemented with proofs of
memory safety, and soon [?] should have functional correctness proofs
too. Additionally, a "nicer" interface will be written so as to hide
away most of the proofs and instead focus on usability, once all the
proofs are done.

You can find the code in the [ind/](ind/) directory. Previous versions
of the proofs can be found by going over the history of this
repository. In particular, `803104cf585` removed a lot of old
stuff. Older versions included code working with F\* `ref`erences, F\*
`buf`fers, Low\* `pointer`s, custom `gpointers`, etc. Additionally,
earlier proofs were based on the `seq` library, and relied heavily on
a quantifier based proof style.

The latest version of the proof uses an approach heavily dependent on
the concept of "separation of concerns". In addition, it purely relies
on inductive definitions of validity, rather than quantifier based
definitions. While this makes certain proofs cumbersome, it
significantly improves proof performance, since the proofs can now be
directed in certain directions, rather than relying on z3's heuristics
for quantifiers to instantiate correctly. As for the "separation of
concerns" part, any time an operation is to be performed on a `dll`
(doubly linked list), it is first turned into a `fragment` (which
consists of 0 or more `piece`s). These `piece`s themselves are moved
around or manipulated, with every single operation "maintaining
`valid`ity"). Then finally, these are transformed back into a
`dll`. Since only the first and last transformations need to worry
about `dll` validity, these separate out concerns regarding continuity
of the list, as well as properties about the "ends". The validity of a
`piece` and `fragment`, on the other hand, allows controlling things
in a much more easy-to-use way, by having composable operations that
can violate `dll` validity, but maintain `piece` validity. This way,
operations can _temporarily_ violate `dll` validity, perform
manipulations, and then return back to `dll` validity in a sane way.

In addition to the proof style, the current version of the proof also
uses the new Low\* `buffer` and Low\* `modifies` libraries. These are
_tremendously_ helpful in being able to talk about large amounts of
modifications in a sane way.

## How to Read the Proof

Start off from [`DListLowInd.fst`](ind/DListLowInd.fst)'s proof of
`dll_insert_at_head` and read downwards. Whenever you hit upon a lemma
that you don't recognize/understand, read up on that lemma earlier in
the file.

There are some operators (such as `=|>`, `|>`, `@`, etc) that are used
throughout the proofs. These are placed at the start of the file
itself for easy access and understanding.

The [`Utils.fst`](ind/Utils.fst) and
[`Gpointers.fst`](ind/Gpointers.fst) contain useful shorthand or
lemmas regarding lists and `gpointers` respectively. It might be
useful to take a quick glance at these if those respective parts are
unclear.

The aim of `Utils.fst` is to be integrated into [F\*
`master`](https://github.com/FStarLang/FStar/) at some point, so as to
be useful to all users of the `list` library.

## Running the Verifier

Simply go over to the `ind/` directory and run `make` to start off the
verification process. You should receive a `All verification
conditions discharged successfully` after a few minutes, if all went
well.

You _might_ need to update the `Makefile` to your own path of
`kremlib` unless you too are a `jay` :P

Run `make clean` to clear `.checked` files, and `make nuke` to clear
all temporary files form the directory.

## License

To be decided
