sig Node { link: one Node }
pred Cyclic {
 all n: Node | n.^link = Node
}
run Cyclic for 5 Node
