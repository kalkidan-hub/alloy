/*
sig Number {
  succ: lone Number
}
one sig Zero extends Number {}

fact ZeroHasNoPredecessor {
  no n: Number | n.succ = Zero
}

fact SuccInjective {
  succ.~succ in iden
}

fact SuccAcyclic {
  no n: Number | n in n.^succ
}

fun even[]: set Number {
  Zero.*(succ.succ)
}

run {} for 4
*/
abstract sig Node {}
sig Number extends Node {
  succ: one Node
}
one sig Last extends Node {}
one sig Zero extends Number {}

fact ZeroHasNoPredecessor {
  no n: Number | n.succ = Zero
}

fact SuccInjective {
  succ.~succ in iden
}

fact SuccAcyclic {
  no n: Number | n in n.^succ
}

fact Connected {
  Node in Zero.*succ
}

fun even[]: set Number {
  Zero.*(succ.succ)
}

run {} for 6
