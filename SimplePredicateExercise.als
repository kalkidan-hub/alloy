sig Thing {
       x: Int
}
fact ThingIsGreaterThanZero {
  all t: Thing | t.x >= 0
}
pred LessThanThree[t: Thing] { t.x < 25 }
run LessThanThree for 1 but 6 int
