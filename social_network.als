sig User{
follows: set User
}

-- Constraint 1: "No user can follow themselves" (Irreflexivity)
-- Quantified style

fact NoSelfFollower{
	all u: User | u not in u.follows
}

-- Relational Logic style
fact NoSelfFollwerRelation{
	no(iden & follows)
}

-- Constraint 2: "Mutual followers"
pred isMutual[u1: User, u2: User]{
	u2 in u1.follows and u1 in u2.follows
}
-- Constraint 3: "Indirect reachability using Transitive Closure"

pred canReach[u1: User, u2: User]{
	u2 in u1.^follows
}

-- Example constraint
pred allMutual{
	all u1, u2: User | u1 != u2 implies u2 in u1.follows
}

run {} for 4
run isMutual for 4
run canReach for 4
-- run allMutual for 6
