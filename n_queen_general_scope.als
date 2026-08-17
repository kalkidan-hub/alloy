sig Col {}
fun N: Int { #Col }

one sig Board {
	queen: Int -> lone Int
}

fact Domain {
	all c: Int | (c >= 0 and c < N) implies one Board.queen[c]
	all c: Int | (c < 0 or c >= N) implies no Board.queen[c]
}

fact RowRange {
	all c: Int | (c >= 0 and c < N) implies (Board.queen[c] >= 0 and Board.queen[c] < N)
}

fact NoSameRow {
	all c1, c2: Int | (c1 in Board.queen.univ and c2 in Board.queen.univ and c1 != c2) implies
	Board.queen[c1] != Board.queen[c2]
}

fact NoDiagonal {
	all c1, c2: Int | (c1 in Board.queen.univ and c2 in Board.queen.univ and c1 != c2) implies
	not (
		minus[Board.queen[c1], Board.queen[c2]] = minus[c1, c2]
		or
		minus[Board.queen[c1], Board.queen[c2]] = minus[0, minus[c1, c2]]
	)
}

fun q[c: Int]: Int { Board.queen[c] }

-- General lexicographic ≤, works for any N (no unrolling needed)
pred lexLessOrEqual[q1: Int -> lone Int, q2: Int -> lone Int] {
	q1 = q2
	or
	some c: Int | {
		c >= 0 and c < N
		q1[c] < q2[c]
		all c2: Int | (c2 >= 0 and c2 < c) implies q1[c2] = q2[c2]
	}
}

fact FullSymmetryBreaking {
	let
		m       = minus[N, 1],
		q_horiz = { c: Int, r: Int | c >= 0 and c < N and r = minus[m, Board.queen[c]] },
		q_vert  = { c: Int, r: Int | c >= 0 and c < N and r = Board.queen[minus[m, c]] },
		q_180   = { c: Int, r: Int | c >= 0 and c < N and r = minus[m, Board.queen[minus[m, c]]] },
		q_diag  = { c: Int, r: Int | c >= 0 and c < N and Board.queen[r] = c },
		q_anti  = { c: Int, r: Int | c >= 0 and c < N and Board.queen[minus[m, r]] = minus[m, c] },
		q_90    = { c: Int, r: Int | c >= 0 and c < N and Board.queen[r] = minus[m, c] },
		q_270   = { c: Int, r: Int | c >= 0 and c < N and Board.queen[minus[m, r]] = c }
	| {
		lexLessOrEqual[Board.queen, q_horiz]
		lexLessOrEqual[Board.queen, q_vert]
		lexLessOrEqual[Board.queen, q_180]
		lexLessOrEqual[Board.queen, q_diag]
		lexLessOrEqual[Board.queen, q_anti]
		lexLessOrEqual[Board.queen, q_90]
		lexLessOrEqual[Board.queen, q_270]
	}
}

run {} for exactly 1  Col, 6 int
run {} for exactly 2  Col, 6 int
run {} for exactly 3  Col, 6 int
run {} for exactly 4  Col, 6 int
run {} for exactly 5  Col, 6 int
run {} for exactly 6  Col, 6 int
run {} for exactly 7  Col, 6 int
run {} for exactly 8  Col, 6 int
run {} for exactly 9  Col, 6 int
run {} for exactly 10 Col, 6 int
