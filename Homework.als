sig Node{
	next: lone Node
}
pred Cyclic{
all n: Node | n in n.^next
}

run Cyclic for 4
