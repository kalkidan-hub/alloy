sig Node{
	next: lone Node
}
pred SinglyLinked{
	all n: Node | lone n.next
}
pred Acyclic{
	all n: Node | n ! in n.^next
}

run Acyclic

