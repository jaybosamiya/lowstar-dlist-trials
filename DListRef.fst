module DListRef

open FStar
open FStar.Ghost
open FStar.Option
open FStar.Seq
open FStar.Ref

#set-options "--use_two_phase_tc true"

unopteq
(** Node of a doubly linked list *)
type dlist (t:Type0) = {
  (* forward link *)
  flink: option (ref (dlist t));
  (* backward link *)
  blink: option (ref (dlist t));
  (* payload *)
  p: t;
}

unopteq
(** Doubly linked list head *)
type dlisthead (t:Type0) ={
  lhead: option (ref (dlist t));
  ltail: option (ref (dlist t));
  nodes: erased (seq (dlist t));
}

(** Initialize an element of a doubly linked list *)
val empty_entry: #t:Type -> payload:t -> dlist t
let empty_entry #t payload =
  { flink = None ; blink = None ; p = payload }

(** Initialize a doubly linked list head *)
val empty_list: #t:Type -> dlisthead t
let empty_list #t =
  { lhead = None ; ltail = None ; nodes = hide createEmpty }

val getSome: (a:option 'a{isSome a}) -> (b:'a{a == Some b})
let getSome a = Some?.v a

unfold let (@) (a:ref 't) (h0:heap) = sel h0 a
unfold let (^@) (a:option (ref 't){isSome a}) (h0:heap) = (getSome a) @ h0

unfold let (.[]) (s:seq 'a) (n:nat{n < length s}) = index s n

val not_aliased: #t:Type -> (a:option (ref t)) -> (b:option (ref t)) -> Type0
let not_aliased #t a b =
  let _ = () in // UGLY workaround. See https://github.com/FStarLang/FStar/issues/638
  isNone a \/ isNone b \/
  addr_of (getSome a) <> addr_of (getSome b)

val not_aliased0: #t:Type -> (a:ref t) -> (b:option (ref t)) -> Type0
let not_aliased0 #t a b =
  let _ = () in // UGLY workaround. See https://github.com/FStarLang/FStar/issues/638
  isNone b \/
  addr_of a <> addr_of (getSome b)

val dlist_is_valid: #t:Type -> n:dlist t -> Type0
let dlist_is_valid #t n =
  not_aliased n.flink n.blink

val flink_valid: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let flink_valid #t h0 h =
  let nodes = reveal h.nodes in
  let len = length nodes in
  (forall i. {:pattern (nodes.[i]).flink}
     ((0 <= i /\ i < len - 1) ==>
      isSome (nodes.[i]).flink /\
      (nodes.[i]).flink^@h0 == nodes.[i+1]))

val blink_valid: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let blink_valid #t h0 h =
  let nodes = reveal h.nodes in
  let len = length nodes in
  (forall i. {:pattern (nodes.[i]).blink}
     ((1 <= i /\ i < len) ==>
      isSome (nodes.[i]).blink /\
      (nodes.[i]).blink^@h0 == nodes.[i-1]))

val dlisthead_ghostly_connections: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let dlisthead_ghostly_connections #t h0 h =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  ~empty ==> (
    isSome h.lhead /\ isSome h.ltail /\
    isNone (h.lhead^@h0).blink /\
    isNone (h.ltail^@h0).flink /\
    h.lhead^@h0 == nodes.[0] /\
    h.ltail^@h0 == nodes.[len-1])

val elements_dont_alias1: #t:Type -> h:dlisthead t -> Type0
let elements_dont_alias1 #t h =
  let nodes = reveal h.nodes in
  (forall i j. {:pattern (not_aliased (nodes.[i]).flink (nodes.[j]).flink)}
     i <> j ==> not_aliased (nodes.[i]).flink (nodes.[j]).flink)

val elements_dont_alias2: #t:Type -> h:dlisthead t -> Type0
let elements_dont_alias2 #t h =
  let nodes = reveal h.nodes in
  (forall i j. {:pattern (not_aliased (nodes.[i]).blink (nodes.[j]).blink)}
     i <> j ==> not_aliased (nodes.[i]).blink (nodes.[j]).blink)

val elements_dont_alias: #t:Type -> h:dlisthead t -> Type0
let elements_dont_alias #t h =
  let _ = () in // UGLY workaround. See https://github.com/FStarLang/FStar/issues/638
  elements_dont_alias1 h /\
  elements_dont_alias2 h

val elements_are_valid: #t:Type -> h:dlisthead t -> Type0
let elements_are_valid #t h =
  let nodes = reveal h.nodes in
  (forall i. {:pattern (dlist_is_valid nodes.[i])}
     dlist_is_valid nodes.[i])

val dlisthead_is_valid: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let dlisthead_is_valid #t h0 h =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  (empty ==> isNone h.lhead /\ isNone h.ltail) /\
  (~empty ==> dlisthead_ghostly_connections h0 h /\
              flink_valid h0 h /\
              blink_valid h0 h) /\
  elements_are_valid h /\
  elements_dont_alias h

let test1 () : Tot unit = assert (forall h0 t. dlisthead_is_valid h0 (empty_list #t))

val singletonlist: #t:eqtype -> e:ref (dlist t) ->
  ST (dlisthead t)
  (requires (fun _ -> True))
  (ensures (fun h0 y h1 -> modifies (only e) h0 h1 /\ dlisthead_is_valid h1 y))
let singletonlist #t e =
  e := { !e with blink = None; flink = None };
  { lhead = Some e ; ltail = Some e ; nodes = hide (Seq.create 1 (!e)) }

let member_of (#t:eqtype) (h0:heap) (h:dlisthead t) (e:ref (dlist t)) : GTot bool =
  Seq.mem (e@h0) (reveal h.nodes)

let has_nothing_in (#t:eqtype) (h0:heap) (h:dlisthead t) (e:ref (dlist t)) : GTot Type0 =
  (~(member_of h0 h e)) /\
  (let nodes = reveal h.nodes in
   (forall i. {:pattern (nodes.[i]).flink}
      (not_aliased0 e (nodes.[i]).flink /\
       not_aliased (e@h0).flink (nodes.[i]).flink /\
       not_aliased (e@h0).blink (nodes.[i]).flink)) /\
   (forall i. {:pattern (nodes.[i]).blink}
      (not_aliased0 e (nodes.[i]).blink) /\
      not_aliased (e@h0).flink (nodes.[i]).blink /\
      not_aliased (e@h0).blink (nodes.[i]).blink))

type nonempty_dlisthead t = (h:dlisthead t{isSome h.lhead /\ isSome h.ltail})

unfold let (~.) (#t:Type) (a:t) : Tot (erased (seq t)) = hide (Seq.create 1 a)
unfold let (^+) (#t:Type) (a:t) (b:erased (seq t)) : Tot (erased (seq t)) = elift2 Seq.cons (hide a) b

val dlisthead_make_valid_singleton: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 ->
         isNone (h.lhead^@h0).flink /\ isNone (h.lhead^@h0).blink))
    (ensures (fun h1 y h2 -> modifies_none h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_make_valid_singleton #t h =
  let Some e = h.lhead in
  { h with ltail = h.lhead ; nodes = ~. !e }

unfold let ghost_tail (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 0}) : Tot (erased (seq t)) =
  hide (Seq.tail (reveal s))

val ghost_tail_properties :
  #t:Type ->
  s:erased (seq t){Seq.length (reveal s) > 0} ->
  Lemma (
    let l = Seq.length (reveal s) in
    let t = ghost_tail s in
    let s0 = reveal s in
    let t0 = reveal t in
    Seq.length t0 = Seq.length s0 - 1 /\
    (forall i j. {:pattern (t0.[i] == s0.[j])}
       j = i + 1 /\ 0 <= i /\ i < Seq.length t0 ==> t0.[i] == s0.[j]))
let ghost_tail_properties #t s = ()

#set-options "--z3rlimit 1 --detail_errors --z3rlimit_factor 20"

val ghost_append_properties: #t:Type -> a:t -> b:erased (seq t) ->
  Lemma (let r = a ^+ b in
         forall i j. {:pattern ((reveal b).[i] == (reveal r).[j])}
           j = i + 1 /\ 0 <= i /\ i < length (reveal b) ==> (reveal b).[i] == (reveal r).[j])
let ghost_append_properties #t a b = ()

val dlisthead_update_head: #t:eqtype -> h:nonempty_dlisthead t -> e:ref (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid (e@h0) /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies (e ^+^ (getSome h.lhead)) h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_update_head (#t:eqtype) (h:nonempty_dlisthead t) (e:ref (dlist t)) =
  let h1 = ST.get () in
  let Some n = h.lhead in
  e := { !e with blink = None; flink = Some n };
  let previously_singleton = compare_addrs n (getSome h.ltail) in
  n := { !n with blink = Some e };
  if previously_singleton
  then (
    let y = { lhead = Some e ; ltail = Some n ; nodes = !e ^+ ~. !n } in
    let h2 = ST.get () in
    assert(let h = y in let h0 = h2 in
           // let nodes = reveal h.nodes in
           // let len = length nodes in
           // let empty = (len = 0) in
           // dlisthead_ghostly_connections h0 h /\
           // flink_valid h0 h /\
           // blink_valid h0 h /\
           // elements_are_valid h /\
           // elements_dont_alias1 h /\
           // elements_dont_alias2 h /\
/// -------------------------------------------------------------------------------------------
/// -------------------------------------------------------------------------------------------
           True);
           // (empty ==> isNone h.lhead /\ isNone h.ltail) /\
           // (~empty ==> dlisthead_ghostly_connections h0 h /\
           //             flink_valid h0 h /\
           //             blink_valid h0 h)); // /\
           // elements_are_valid h /\
           // elements_dont_alias h);
    // admit ();
    y
  ) else (
    admit ();
    let y = { lhead = Some e ; ltail = h.ltail ; nodes = !e ^+ !n ^+ (ghost_tail h.nodes) } in
    let h2 = ST.get () in
    // assert (y.ltail == h.ltail);
    // assert (h.ltail^@h1 == h.ltail^@h2);
    // assert (isSome y.ltail);
    // assert (getSome y.ltail == getSome y.ltail);
    // assert (let (a : _ {isSome a}) = y.ltail in sel h2 (getSome a) == sel h2 (getSome a));
    // The (a: _ {...}) is a workaround for the two phase type checker error
    // assert (let (a : _ {isSome a}) = y.ltail in sel h1 (getSome a) == sel h2 (getSome a));
    // assert (let (a : _ {isSome a}) = y.ltail in a^@h2 == h.ltail^@h1);
    // assert (let hnodes, ynodes = reveal h.nodes, reveal y.nodes in
    //   forall i j. {:pattern (hnodes.[i] == ynodes.[j])}
    //     j = i + 1 /\ i > 1 /\ j < length ynodes ==> hnodes.[i] == ynodes.[j]);
    // assert (Seq.length (reveal h.nodes) + 1 = Seq.length (reveal y.nodes));
    // admit ();
    // assert (Seq.last (reveal h.nodes) == Seq.last (reveal y.nodes)); // this fails for some reason
    // admit ();
    // assert (let nodes = reveal y.nodes in
    //         let len = length nodes in
    //         y.ltail^@h2 == nodes.[len-1]); // Unable to prove this for some reason
    // // admit ();
    // assert (dlisthead_ghostly_connections h2 y);
    // assert (flink_valid h2 y);
    // assert (blink_valid h2 y);
    admit ();
    y
  )

let test () = ()

(*
val insertHeadList: #t:eqtype -> h:dlisthead t -> e:ref (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ ~(member_of h0 h e)))
    (ensures (fun _ y h2 -> dlisthead_is_valid h2 y))
let insertHeadList #t h e =
  if isNone h.lhead
  then (
    singletonlist e
  ) else (
    let h1 = ST.get () in
    let n = getSome h.lhead in
    n := { !n with blink = Some e };
    let h1' = ST.get () in
    e := { !e with blink = None ; flink = Some n };
    let ghoste = hide !e in
    let nodes = elift2 cons ghoste h.nodes in
    let y = { lhead = Some e ; ltail = h.ltail ; nodes = nodes } in
    let h2 = ST.get () in
    // assert (isSome y.lhead /\ isSome y.ltail);
    // assert (isNone (y.lhead^@h2).blink);
    assert (isNone (y.ltail^@h2).flink); // OBSERVE
    // assert (y.lhead^@h2 == (reveal y.nodes).[0]);
    assert (h.ltail^@h1 == (reveal h.nodes).[length (reveal h.nodes) - 1]);
    assert (h.ltail^@h1' == (reveal h.nodes).[length (reveal h.nodes) - 1]); // this fails. reason: what if the dlisthead is a singleton when we begin?
    admit ();
    assert (
      let nodes = reveal y.nodes in
      let len = length nodes in
      let empty = (len = 0) in
      ((isSome y.lhead /\ isSome y.ltail) /\
       isNone (y.lhead^@h2).blink /\
       isNone (y.ltail^@h2).flink /\
        (y.lhead^@h2 == nodes.[0]) /\
        (y.ltail^@h2 == nodes.[len-1]) /\
        // (forall i. {:pattern (nodes.[i]).blink}
        //    ((1 <= i /\ i < len) ==>
        //     isSome (nodes.[i]).blink /\
        //     (nodes.[i]).blink^@h2 == nodes.[i-1])) /\
        // (forall i. {:pattern (nodes.[i]).flink}
        //    ((0 <= i /\ i < len - 1) ==>
        //     isSome (nodes.[i]).flink /\
        //     (nodes.[i]).flink^@h2 == nodes.[i+1])) /\
        True)
     );
     admit ();
     y
  )

*)
