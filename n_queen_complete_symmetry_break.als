one sig Board {
	queen: Int -> lone Int
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
		minus[Board.queen[c1], Board.queen[c2]] = minus[c1, c2]
		or
		minus[Board.queen[c1], Board.queen[c2]] = minus[0, minus[c1, c2]]
	)
}

-- helper function: returns row position at column c
fun q[c: Int]: Int {
	Board.queen[c]
}

-- Lexicographical comparison of two configurations represented as functions
pred lexLessOrEqual[q1: Int -> lone Int, q2: Int -> lone Int] {
	q1[0] < q2[0] or (q1[0] = q2[0] and (
	q1[1] < q2[1] or (q1[1] = q2[1] and (
	q1[2] < q2[2] or (q1[2] = q2[2] and (
	q1[3] < q2[3] or (q1[3] = q2[3] and (
	q1[4] < q2[4] or (q1[4] = q2[4] and (
	q1[5] < q2[5] or (q1[5] = q2[5] and (
	q1[6] < q2[6] or (q1[6] = q2[6] and (
	q1[7] <= q2[7]))))))))))))))
}

fact FullSymmetryBreaking {
	let 
		-- 1. Horizontal reflection
		q_horiz = { c: Int, r: Int | c >= 0 and c < 8 and r = minus[7, Board.queen[c]] },
		
		-- 2. Vertical reflection
		q_vert  = { c: Int, r: Int | c >= 0 and c < 8 and r = Board.queen[minus[7, c]] },
		
		-- 3. 180 degree rotation
		q_180   = { c: Int, r: Int | c >= 0 and c < 8 and r = minus[7, Board.queen[minus[7, c]]] },
		
		-- 4. Transpose / Main Diagonal reflection: (c, r) -> (r, c)
		-- The new queen at column 'c' sits at row 'r' if original had queen at column 'r' with row 'c'
		q_diag  = { c: Int, r: Int | c >= 0 and c < 8 and Board.queen[r] = c },
		
		-- 5. Anti-diagonal reflection
		q_anti  = { c: Int, r: Int | c >= 0 and c < 8 and Board.queen[minus[7, r]] = minus[7, c] },
		
		-- 6. 90 degree rotation (counter-clockwise)
		q_90    = { c: Int, r: Int | c >= 0 and c < 8 and Board.queen[r] = minus[7, c] },
		
		-- 7. 270 degree rotation (counter-clockwise)
		q_270   = { c: Int, r: Int | c >= 0 and c < 8 and Board.queen[minus[7, r]] = c }
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

run {} for 8 but 6 int
