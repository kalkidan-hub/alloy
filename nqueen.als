open util/integer

one sig Board {
    queen: Int -> lone Int   -- partial function now, no forced totality over all Int
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
    all c1, c2: Int | (c1 in Board.queen.univ and c2 in Board.queen.univ and c1 < c2) implies {
        -- Instead of (q1 - q2 = c1 - c2), use addition:
        -- q1 - q2 != c1 - c2  =>  q1 + c2 != q2 + c1
        plus[Board.queen[c1], c2] != plus[Board.queen[c2], c1]
        
        -- q1 - q2 != c2 - c1  =>  q1 + c1 != q2 + c2
        plus[Board.queen[c1], c1] != plus[Board.queen[c2], c2]
    }
}

run {} for 8 but 4 int
