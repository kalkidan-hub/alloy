sig Name {
    address: set Address
}
sig Address {}

-- predicate calculus style
fact atMostOneAddress{
	all n: Name, d, e: Address |
	    (n->d in address and n->e in address) => d = e
}

-- run atMostOneAddress for 3

-- navigation expression style
assert navigateAtMostOneAddress {
	all n:Name | lone n.address
}

assert  relationalAtMostOneAddress {
	no ~address.address - iden
}

check relationalAtMostOneAddress 
check navigateAtMostOneAddress
