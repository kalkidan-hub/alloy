module nqueens

open util/integer

sig Queen {
  row: one Int,
  col: one Int
}

fun boardSize: one Int {
  #Queen
}
fun myAbs[n: Int]: Int { n < 0 => negate[n] else n }

pred validBoard {
  let n = boardSize |
    all q: Queen |
      q.row >= 0 and q.row < n and
      q.col >= 0 and q.col < n

  // Exactly one queen in every row and column.
  all disj q1, q2: Queen |
    q1.row != q2.row and
    q1.col != q2.col

  // No two queens share a diagonal.
  all disj q1, q2: Queen |
    myAbs[q1.row - q2.row] != myAbs[q1.col - q2.col]
}

pred show {
  validBoard
}

run show for exactly 8 Queen, 5 Int
