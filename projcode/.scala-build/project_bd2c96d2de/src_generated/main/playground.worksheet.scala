



object `playground.worksheet` {
/*<script>*/def decreases[A](a: A): Unit = ()

extension [A](l: List[A]) {
  def content: Set[A] = l.toSet
}

sealed abstract class Distance
case object Inf extends Distance
case class Real(i: BigInt) extends Distance { require(i >= 0) }

extension (inline i: Int) {
  inline def toDist: Distance =
    require(i >= 0)
    Real(BigInt(i))
}

extension (self: Distance) {
  def <(that: Distance): Boolean = (self, that) match
    case (Inf, Inf)         => false
    case (Real(_), Inf)     => true
    case (Inf, Real(_))     => false
    case (Real(l), Real(r)) => l < r

  def +(that: Distance): Distance = (self, that) match
    case (Real(l), Real(r)) => Real(l + r)
    case _                  => Inf
}

// def noDuplicates[A](l: List[(Int, A)]): Boolean = l match {
//   case Nil          => true
//   case (k, v) :: xs => (xs.get(k) == None) && noDuplicates(xs)
// }

extension [A](self: List[(Int, A)]) {
  def update(x: (Int, A)): List[(Int, A)] = {
    // require(noDuplicates(self))
    self match
      case Nil                      => Nil
      case (i, v) :: t if i == x._1 => (i, x._2) :: t
      case h :: t                   => h :: t.update(x)
  } /* ensuring (res =>
    res.map(_._1) == self.map(_._1) &&
      res.size == self.size &&
      (res.get(x._1) match
        case Some(v) => v == x._2
        case None    => res == self
      )
  ) */

  def get(i: Int): Option[A] = self match
    case Nil         => None
    case (h, v) :: t => if h == i then Some(v) else t.get(i)
}

extension [A, B](self: List[(Int, A, B)]) {
  def update(x: (Int, A, B))(using (A, B)): List[(Int, A, B)] = {
    // require(noDuplicates(self))
    self match
      case Nil                         => Nil
      case (i, _, _) :: t if i == x._1 => (i, x._2, x._3) :: t
      case h :: t                      => h :: t.update(x)
  } /* ensuring (res =>
    res.map(_._1) == self.map(_._1) &&
      res.size == self.size &&
      (res.get(x._1) match
        case Some(v) => v == x._2
        case None    => res == self
      )
  ) */

  def get(i: Int)(using (A, B)): Option[(A, B)] = self match
    case Nil            => None
    case (h, v, z) :: t => if h == i then Some(v -> z) else t.get(i)
}

type Node = (Int, Distance, Option[Int])

def minTrans(l: List[Node], m: Node, n: Node): List[Node] = {
//   require(l.forall(z => m._2 <= z._2) && n._2 <= m._2)
  l match
    case Nil    => List(m)
    case h :: t =>
      //   assert(m._2 <= h._2)
      //   assert(n._2 <= h._2)
      h :: minTrans(t, m, n)
} /* ensuring (res =>
  res.size == l.size + 1 &&
    // res.content == l.content ++ Set(m) &&
    res.forall(z => n._2 <= z._2)
) */

def minInv(l: List[Node], m: Node, n: Node): List[Node] = {
//   require(l.forall(z => m._2 <= z._2) && m._2 <= n._2)
  l match
    case Nil    => List(n)
    case h :: t =>
      //   assert(m._2 <= h._2)
      h :: minInv(t, m, n)
} /* ensuring (res =>
  res.size == l.size + 1 &&
    // res.content == l.content ++ Set(n) &&
    res.forall(z => m._2 <= z._2)
) */

def getMinAux(
    min: Node,
    rest: List[Node],
    seen: List[Node]
): (Node, List[Node]) = {
  decreases(rest.size)
//   require(seen.forall(n => min._2 <= n._2))
  rest match
    case Nil => (min, seen)
    case c :: xs =>
      if c._2 < min._2 then getMinAux(c, xs, minTrans(seen, min, c))
      else getMinAux(min, xs, minInv(seen, min, c))
} /* ensuring (res =>
  res._2.size == rest.size + seen.size &&
    // res._2.content ++ Set(res._1) == rest.content ++ seen.content ++ Set(min) &&
    res._2.forall(n => res._1._2 <= n._2)
) */

// extract min from list
def getMin(l: List[Node]): (Node, List[Node]) = {
  require(l != Nil)
  l match
    case h :: Nil => (h, Nil)
    case h :: t   => getMinAux(h, t, Nil)
} /* ensuring (res =>
  res._2.size == l.size - 1 &&
    res._2.content ++ Set(res._1) == l.content &&
    res._2.forall(n => res._1._2 <= n._2)
) */

// def prepareProp(
//     res: List[Node],
//     graph: List[(Int, List[Node])],
//     start: Int
// ): Boolean =
//   res.size == graph.size &&
//   res.map(_._1) == graph.map(_._1) &&
//   (res.get(start) match {
//     case Some(d) => d == Real(0)
//     case None    => res.forall(_._2 == Inf)
//   })

def prepareAux(
    graph: List[(Int, List[Node])],
    start: Int
): List[Node] = {
  graph match
    case Nil => Nil
    case (v, _) :: xs if v == start =>
      (v, Real(0), None) :: prepareAux(xs, start)
    case (v, _) :: xs => (v, Inf, None) :: prepareAux(xs, start)
} /* ensuring (res => prepareProp(res, graph, start)) */

case class Graph(graph: List[(Int, List[(Int, Distance)])]) {
//   require(noDuplicates(graph) && graph.forall(e => noDuplicates(e._2)))

  // distance between nodes
  def distance(u: Int, v: Int): Distance = {
    graph.get(u).flatMap(_.get(v)) match
      case None    => Inf
      case Some(d) => d
  }

  // update distant to node tar (when at bode cur)
  def updateDist(cur: Node, tar: Node): Node = {
    val nd = cur._2 + distance(cur._1, tar._1)
    if nd < tar._2 then (tar._1, nd, Some(cur._1))
    else (tar._1, tar._2, tar._3)
  } /* ensuring (_._2 <= tar._2) */

  // update distance from cur
  def iterOnce(cur: Node, rest: List[Node]): List[Node] = {
    decreases(rest.size)
    rest match {
      case Nil    => Nil
      case h :: t => updateDist(cur, h) :: iterOnce(cur, t)
    }
  } /* ensuring (res =>
    res.size == rest.size &&
      res
        .zip(rest)
        .forall((y, x) =>
          y._1 == x._1 && y._2 <= x._2
        ) // updated dists should be smaller
  ) */

  // dijkstra main loop
  def iterate(seen: List[Node], future: List[Node]): List[Node] = {
    decreases(future.size)
    future match
      case Nil => seen
      case fu @ (_ :: _) =>
        val (h, t) = getMin(fu)
        iterate(h :: seen, iterOnce(h, t))
  } // ensuring (res => res.size == seen.size + future.size)

  // init dist queue
  def prepare(start: Int): List[Node] = {
    prepareAux(graph.map((n, a) => n -> a.map((i, d) => (i, d, None))), start)
  } /* ensuring (res =>
    prepareProp(
      res,
      graph.map((n, a) => n -> a.map((i, d) => (i, d, None))),
      start
    )
  ) */

  def dijkstra(start: Int): List[Node] = {
    iterate(Nil, prepare(start))
  }

}

val g = Graph(
  List(
    (1, List(2 -> 1.toDist, 3 -> 3.toDist)),
    (2, List(4 -> 5.toDist, 3 -> 1.toDist)),
    (3, List(4 -> 2.toDist)),
    (4, Nil),
    (5, List(4 -> 2.toDist))
  )
)

given (Distance, Option[Int]) = null

val (h, t) = getMin(g.prepare(1))

g.iterOnce(h, t)

g.dijkstra(1).get(4)
/*</script>*/ /*<generated>*/
def args = `playground.worksheet_sc`.args$
  /*</generated>*/
}

object `playground.worksheet_sc` {
  private var args$opt0 = Option.empty[Array[String]]
  def args$set(args: Array[String]): Unit = {
    args$opt0 = Some(args)
  }
  def args$opt: Option[Array[String]] = args$opt0
  def args$: Array[String] = args$opt.getOrElse {
    sys.error("No arguments passed to this script")
  }
  def main(args: Array[String]): Unit = {
    args$set(args)
    `playground.worksheet`.hashCode() // hasCode to clear scalac warning about pure expression in statement position
  }
}

