// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Rustan Leino
// 12 April 2015
// VerifyThis 2015
// Problem 3 -- Dancing Links


function last<T>(s:seq<T>) : T
	requires |s| > 0;
{
	s[|s|-1]
}

function all_but_last<T>(s:seq<T>) : seq<T>
	requires |s| > 0;
{
	s[..|s|-1]
}

class Node<T> {
	var L: Node?<T>
	var R: Node?<T>
	var payload:T
	constructor (p:T)
		ensures payload == p;
	{
		payload := p;
	}
}

class DoublyLinkedList<T> {
	ghost var Nodes: seq<Node<T>>  // sequence of nodes in the linked list
	var head:Node?<T>
	var tail:Node?<T>

	// Valid() says that the data structure is a proper doubly linked list
	// TODO: Consider making this opaque, since clients shouldn't need to care about it
	predicate Valid()
		reads this, Nodes
	{
		(|Nodes| == 0 <==> head == tail == null) &&
		(|Nodes| > 0 ==>
			head == Nodes[0] && tail == last(Nodes) &&
			Nodes[0].L == null &&  last(Nodes).R == null &&
			(forall i {:trigger Nodes[i].L} :: 1 <= i < |Nodes| ==> Nodes[i].L == Nodes[i-1]) &&
			(forall i {:trigger Nodes[i].R} :: 0 <= i < |Nodes|-1 ==> Nodes[i].R == Nodes[i+1])
		) &&
		forall i,j :: 0 <= i < j < |Nodes| ==> Nodes[i] != Nodes[j]  // this is actually a consequence of the previous conditions
	}
	// This constructor just shows that there is a way to create a doubly linked list.  It accepts
	// as an argument the sequences of Nodes to construct the doubly linked list from.  The constructor
	// will change all the .L and .R pointers of the given nodes in order to create a properly
	// formed list.
	constructor (nodes: seq<T>)
		ensures Valid()
		ensures fresh(Nodes)
		ensures |Nodes| == |nodes|
		ensures forall i :: 0 <= i < |Nodes| ==> Nodes[i].payload == nodes[i]
	{
		ghost var Nodes' := [];  // Workaround restriction that we can't mention Nodes in an invariant
		if nodes != [] {
			var prev := new Node(nodes[0]);
			var n := 1;
			var new_head := prev; // Workaround restriction that we can't mention head in an invariant
			Nodes' := [prev];
			prev.L, prev.R := null, null;
			while n < |nodes|
				invariant 1 <= n <= |nodes|
				invariant n == |Nodes'|
				invariant Nodes'[0].L == null
				invariant prev == Nodes'[n-1] && prev.R == null
				invariant forall i :: 1 <= i < n ==> Nodes'[i].L == Nodes'[i-1]
				invariant forall i :: 0 <= i < n-1 ==> Nodes'[i].R == Nodes'[i+1]
				invariant forall i :: 0 <= i < n ==> Nodes'[i].payload == nodes[i]
				invariant forall i, j :: 0 <= i < j < |Nodes'| ==> Nodes'[i] != Nodes'[j];
				invariant new_head == Nodes'[0]
				invariant fresh(Nodes')
			{
				var current := new Node(nodes[n]);
				current.L, prev.R, prev := prev, current, current;
				Nodes' := Nodes' + [current];
				prev.R := null;
				n := n + 1;
			}
			head := new_head;
			tail := prev;
		} else {
			head := null;
			tail := null;
		}
		Nodes := Nodes';
	}

	method IsEmpty() returns (b:bool)
		requires Valid();
		ensures b <==> (|Nodes| == 0);
	{
		b := (head == null && tail == null);
	}

	method Remove(x: Node<T>) returns (ghost k: int)
		requires Valid()
		requires x in Nodes
		modifies this, Nodes
		ensures Valid()
		ensures 0 <= k < |old(Nodes)| && x == old(Nodes)[k]
		ensures Nodes == old(Nodes)[..k] + old(Nodes)[k+1..]
		ensures x.L == old(x.L) && x.R == old(x.R) && x.payload == old(x.payload)
		ensures forall n :: n in (Nodes) ==> n.payload == old(n.payload)
	{
		k :| 0 <= k < |Nodes| && Nodes[k] == x;
		if (x.L == null && x.R == null) {
			Nodes := [];
			head := null;
			tail := null;
		} else if (x.L == null) {
			assert k == 0;
			x.R.L := null;
			head := x.R;
			Nodes := Nodes[1..];
		} else if (x.R == null) {
			assert k == |Nodes| - 1;
			x.L.R := null;
			tail := x.L;
			Nodes := Nodes[..|Nodes|-1];
		} else {
			x.R.L := x.L;
			x.L.R := x.R;
			Nodes := Nodes[..k] + Nodes[k+1..];
		}
	}

	method InsertHead(x:Node<T>)
		requires Valid()
		requires !(x in Nodes)
		modifies this, Nodes, x
		ensures Valid()
		ensures Nodes == [x] + old(Nodes)
		ensures x.payload == old(x.payload)
		ensures forall n :: n in old(Nodes) ==> n.payload == old(n.payload)
	{
		if head == null {
			head := x;
			tail := x;
			x.L := null;
			x.R := null;
			Nodes := [x];
		} else {
			x.R := head;
			x.L := null;
			head.L := x;
			head := x;
			Nodes := [x] + old(Nodes);
		}
	}

	method InsertTail(x:Node<T>)
		requires Valid()
		requires !(x in Nodes)
		modifies this, Nodes, x
		ensures Valid()
		ensures Nodes == old(Nodes) + [x];
		ensures x.payload == old(x.payload)
		ensures forall n :: n in old(Nodes) ==> n.payload == old(n.payload)
	{
		if tail == null {
			head := x;
			tail := x;
			x.L := null;
			x.R := null;
			Nodes := [x];
		} else {
			x.L := tail;
			x.R := null;
			tail.R := x;
			tail := x;
			Nodes := old(Nodes) + [x];
		}
	}

	method InsertBefore(x:Node<T>, insertion_point:Node<T>) returns (ghost k:int)
		requires Valid()
		requires !(x in Nodes)
		requires insertion_point in Nodes
		modifies this, Nodes, x
		ensures Valid()
		ensures 0 <= k < old(|Nodes|) &&
						old(Nodes)[k] == old(insertion_point) &&
						Nodes == old(Nodes)[..k] + [x] + old(Nodes)[k..]
		ensures x.payload == old(x.payload)
		ensures forall n :: n in old(Nodes) ==> n.payload == old(n.payload)
	{
		if insertion_point == head {
			k := 0;
			InsertHead(x);
		} else {
			x.L := insertion_point.L;
			x.R := insertion_point;
			insertion_point.L.R := x;
			insertion_point.L := x;
			k :| 0 <= k < |Nodes| && Nodes[k] == insertion_point;
			Nodes := old(Nodes)[..k] + [x] + old(Nodes)[k..];
		}
	}

	method InsertAfter(x:Node<T>, insertion_point:Node<T>) returns (ghost k:int)
		requires Valid()
		requires !(x in Nodes)
		requires insertion_point in Nodes
		modifies this, Nodes, x
		ensures Valid()
		ensures 0 <= k < old(|Nodes|) &&
						old(Nodes)[k] == old(insertion_point) &&
						Nodes == old(Nodes)[..k+1] + [x] + old(Nodes)[k+1..]
		ensures x.payload == old(x.payload)
		ensures forall n :: n in old(Nodes) ==> n.payload == old(n.payload)
	{
		if insertion_point == tail {
			k := |Nodes| - 1;
			InsertTail(x);
		} else {
			x.R := insertion_point.R;
			x.L := insertion_point;
			insertion_point.R.L := x;
			insertion_point.R := x;
			k :| 0 <= k < |Nodes| && Nodes[k] == insertion_point;
			Nodes := old(Nodes)[..k+1] + [x] + old(Nodes)[k+1..];
			// OBSERVE: Unclear why these three are needed once Node has a payload
			assert forall i {:trigger Nodes[i].L} :: 1 <= i < |Nodes| ==> Nodes[i].L == Nodes[i-1];
			assert forall i {:trigger Nodes[i].R} :: 0 <= i < |Nodes|-1 ==> Nodes[i].R == Nodes[i+1];
			assert forall i,j :: 0 <= i < j < |Nodes| ==> Nodes[i] != Nodes[j] ;
		}
	}

	method Append(d:DoublyLinkedList<T>)
		requires Valid()
		requires d.Valid()
		requires forall x :: x in Nodes ==> !(x in d.Nodes)
		requires forall y :: y in d.Nodes ==> !(y in Nodes)
		modifies this, Nodes, d.Nodes
		ensures Valid()
		ensures Nodes == old(Nodes) + old(d.Nodes)
		ensures forall n :: n in old(Nodes) ==> n.payload == old(n.payload)
		ensures forall n :: n in old(d.Nodes) ==> n.payload == old(n.payload)
	{
		if head == null && tail == null {
			head := d.head;
			tail := d.tail;
			Nodes := d.Nodes;
		} else {
			if d.head == null && d.tail == null {
				// Nothing to do here
			} else {
				tail.R := d.head;
				d.head.L := tail;
				assert head in Nodes;      // OBSERVE: Trigger the membership precondition
				assert d.tail in d.Nodes;  // OBSERVE: Trigger the other membership precondition
				Nodes := Nodes + d.Nodes;
				tail := d.tail;

				// OBSERVEs: Trigger the two membership preconditions
				forall i,j | 0 <= i < j < |Nodes|
					ensures Nodes[i] != Nodes[j];
				{
					if i < |old(Nodes)| {
						assert Nodes[i] in old(Nodes);
					} else {
						assert Nodes[i] in old(d.Nodes);
					}
					if j < |old(Nodes)| {
						assert Nodes[j] in old(Nodes);
					} else {
						assert Nodes[j] in old(d.Nodes);
					}
				}
			}
		}
	}
}

method SplitUsing<T>(d:DoublyLinkedList<T>, x:Node<T>) returns (d0:DoublyLinkedList<T>, d1:DoublyLinkedList<T>, ghost k:int)
	requires d.Valid()
	requires x in d.Nodes
	modifies d, d.Nodes
	ensures d0.Valid() && d1.Valid()
	ensures 0 <= k < |old(d.Nodes)| && old(d.Nodes)[k] == x
	ensures old(d.Nodes) == d0.Nodes + d1.Nodes
	ensures old(d.Nodes)[..k] == d0.Nodes
	ensures old(d.Nodes)[k..] == d1.Nodes
	ensures x.payload == old(x.payload)
	ensures forall n :: n in old(d.Nodes) ==> n.payload == old(n.payload)
{
	d0 := new DoublyLinkedList([]);
	d1 := new DoublyLinkedList([]);

	if (d.head == x) {
		d0.head := null;
	} else {
		d0.head := d.head;
	}
	d0.tail := x.L;
	if !(d0.tail == null) {
		d0.tail.R := null;
	}

	d1.head := x;
	x.L := null;
	d1.tail := d.tail;

	k :| 0 <= k < |old(d.Nodes)| && old(d.Nodes)[k] == x;
	d0.Nodes := d.Nodes[..k];
	d1.Nodes := d.Nodes[k..];
}

function reverse<T>(s:seq<T>) : seq<T>
	ensures |reverse(s)| == |s|
{
	if s == [] then []
	else reverse(s[1..]) + [s[0]]
}

/*
function reverse'<T>(s:seq<T>) : seq<T>
	ensures |reverse(s)| == |s|
{
	if s == [] then []
	else [last(s)] + reverse'(all_but_last(s))
}
*/

lemma lemma_reverse_commutes<T>(s:seq<T>, t:seq<T>)
	ensures reverse(s + t) == reverse(t) + reverse(s);
{
	if s == [] {
		assert s + t == t;
	} else {
		var c := s + t;
		calc {
			reverse(s + t);
			reverse(c[1..]) + [c[0]];
			reverse(c[1..]) + reverse([c[0]]);
				{
					assert c[1..] == s[1..] + t;
					lemma_reverse_commutes(s[1..], t);
				}
			reverse(t) + reverse(s[1..]) + reverse([s[0]]);
			reverse(t) + reverse(s);
		}
	}
}

lemma lemma_reverse_reverse<T>(s:seq<Node<T>>)
	decreases |s|
	ensures reverse(reverse(s)) == s
{
	if s == [] {
	} else {
		calc {
			reverse(reverse(s));
			reverse(reverse(s[1..]) + [s[0]]);
			reverse(reverse(s[1..]) + reverse([s[0]]));
				{ lemma_reverse_commutes(reverse(s[1..]), reverse([s[0]])); }
			[s[0]] + reverse(reverse(s[1..]));
				{ lemma_reverse_reverse(s[1..]); }
			[s[0]] + s[1..];
			s;
		}
	}
}

lemma lemma_reverse_membership<T>(s:seq<Node<T>>, x:Node<T>)
	requires x in s
	ensures  x in reverse(s)
{
}

lemma lemma_reverse_non_membership<T>(s:seq<Node<T>>, x:Node<T>)
	requires !(x in s)
	ensures  x !in reverse(s)
{

}

lemma lemma_reverse_commutes_Node<T>(s:seq<Node<T>>, t:seq<Node<T>>)
	ensures reverse(s + t) == reverse(t) + reverse(s);
{
	lemma_reverse_commutes(s, t);
}

lemma lemma_Reverse_helper<T>(s:seq<Node<T>>, t:seq<Node<T>>, u:seq<Node<T>>, x:Node<T>)
	requires s == reverse(t) + [x]
	requires [x] + t == u
	ensures s == reverse(u)
{
	calc {
			s;
			reverse(t) + [x];
				{ assert [x] == reverse([x]); }
			reverse(t) + reverse([x]);
				{ lemma_reverse_commutes_Node([x], t); }
			reverse([x] + t);
				{ assert [x] + t == u; }
			reverse(u);
	}
}

method Reverse<T>(d:DoublyLinkedList<T>)
	requires d.Valid()
	modifies d, d.Nodes
	decreases |d.Nodes|
	ensures  d.Valid()
	ensures  d.Nodes == reverse(old(d.Nodes))
	ensures forall n :: n in old(d.Nodes) ==> n.payload == old(n.payload)
	ensures forall n :: n in old(d.Nodes) <==> n in d.Nodes
{
	var empty := d.IsEmpty();
	if empty {
	} else {
		var h := d.head;
		ghost var k := d.Remove(h);
		calc {
			[h] + d.Nodes;
			[old(d.Nodes)[0]] + old(d.Nodes)[1..];
			old(d.Nodes);
		}
		ghost var old_nodes := d.Nodes;
		lemma_reverse_reverse(old_nodes);
		Reverse(d);
		lemma_reverse_reverse(d.Nodes);

		// Needed to satisfy the modifies check
		forall i | 0 <= i < |d.Nodes|
			ensures d.Nodes[i] in old(d.Nodes);
		{
			lemma_reverse_membership(d.Nodes, d.Nodes[i]);
			lemma_reverse_reverse(old_nodes);
			lemma_reverse_membership(old_nodes, d.Nodes[i]);
		}
		d.InsertTail(h);

		// Prove that d.Nodes == reverse(old(d.Nodes))
		lemma_Reverse_helper(d.Nodes, old_nodes, old(d.Nodes), h);
	}
}

// And here's a Main program that shows that doubly linked lists do exist (well, at least there is one :))
method Main()
{
	var dd := new DoublyLinkedList([0, 1, 2, 3, 4, 5]);
	assert dd.tail.payload == 5;
	var a6 := new Node(6);
	var a7 := new Node(7);
	dd.InsertHead(a6);
	assert a6.payload == 6;
	ghost var old_Nodes := dd.Nodes;
	dd.InsertHead(a7);
	assert a7.payload == 7;
	assert a6 in old_Nodes;
	assert a6.payload == 6;
	assert dd.tail.payload == 5;
}
