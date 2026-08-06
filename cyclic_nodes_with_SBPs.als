open util/ordering[Node]

sig Node {
  link: one Node
}

pred Cyclic {
  all n: Node | n.^link = Node
}

pred canonicalCycle {
  let last = Node - next.Node |
    (all n: Node - last | n.link = n.next) and
    last.link = first
}

run { Cyclic and canonicalCycle } for 5 Node
