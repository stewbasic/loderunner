Consider a simplified version of [Lode Runner](https://en.wikipedia.org/wiki/Lode_Runner)
without enemies or gold, and in which the player can choose when blocks are solidified.
We provide a formal [Coq](https://coq.inria.fr/) proof of the answer to
[this question](https://math.stackexchange.com/q/2594935), namely:
* There is a rectangular stage which allows the player to move from top-left
  to bottom-right and top-right to bottom-left, but not vice versa.
* Such a stage must include ladders and bricks, and those two tiles are also
  sufficient.

