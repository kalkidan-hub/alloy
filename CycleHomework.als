open util/ordering[Node] as ord

abstract sig Node { nxt: lone Node }
one sig List { hd: Node }

fact {
Node = List.hd.*nxt
}

pred Cyclic[l: List] {
l.hd in l.hd.^nxt
}

fact SymmetryBreak {
  List.hd = ord/first
  all n: Node - ord/last | n.nxt = ord/next[n]
  ord/last.nxt = ord/first
}

run { Cyclic[List] } for 7


