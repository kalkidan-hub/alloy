one sig Board {
queen: Int -> lone Int -- partial function now, no forced totality over all Int
}

fact Domain {
	all c: Int | (c >= 0 and c < 8) implies one Board.queen[c]
	all c: Int | (c < 0 or c >= 8) implies no Board.queen[c]
}

fact RowRange {
	all c: Int | (c >= 0 and c < 8) implies (Board.queen[c] >= 0 and Board.queen[c] < 8)
}

fact NoSameRow {
	all c1, c2: Int | (c1 in Board.queen.univ and c2 in Board.queen.univ and c1 != c2) implies
	Board.queen[c1] != Board.queen[c2]
}

fact NoDiagonal {
	all c1, c2: Int | (c1 in Board.queen.univ and c2 in Board.queen.univ and c1 != c2) implies
	not (
		minus[Board.queen[c1],  Board.queen[c2]] = minus[c1, c2]
		or
		minus[Board.queen[c1], Board.queen[c2]] = minus[0, minus[c1, c2]]
	)
}

run {} for 8 but 5 int
