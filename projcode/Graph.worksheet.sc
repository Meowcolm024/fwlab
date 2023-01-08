sealed abstract class Distance
case object Inf extends Distance
case class Real(i: BigInt) extends Distance

extension (i: BigInt) {
  def toDist: Distance =
    Real(i)
}

extension (self: Distance) {
  def <=(that: Distance): Boolean = (self, that) match
    case (Inf, Inf)         => true
    case (Real(_), Inf)     => true
    case (Inf, Real(_))     => false
    case (Real(l), Real(r)) => l <= r

  def +(that: Distance): Distance = {
    (self, that) match
      case (Real(l), Real(r)) => Real(l + r)
      case _                  => Inf
  }
}

def noDuplicates[A](l: List[(Int, A)]): Boolean = l match {
  case Nil          => true
  case (k, v) :: xs => (xs.get(k) == None) && noDuplicates(xs)
}

extension [A](self: List[(Int, A)]) {
  def update(x: (Int, A)): List[(Int, A)] = {
    self match
      case Nil                      => Nil
      case (i, v) :: t if i == x._1 => (i, x._2) :: t
      case h :: t                   => h :: t.update(x)
  }

  def get(i: Int): Option[A] = self match
    case Nil         => None
    case (h, v) :: t => if h == i then Some(v) else t.get(i)
}

type Node = (Int, Distance)

def minTrans(l: List[Node], m: Node, n: Node): List[Node] = {
  require(l.forall(z => m._2 <= z._2) && n._2 <= m._2)
  l match
    case Nil    => m :: Nil
    case h :: t => h :: minTrans(t, m, n)
}

def minInv(l: List[Node], m: Node, n: Node): List[Node] = {
  require(l.forall(z => m._2 <= z._2) && m._2 <= n._2)
  l match
    case Nil    => n :: Nil
    case h :: t => h :: minInv(t, m, n)
}

def getMinAux(
    min: Node,
    rest: List[Node],
    seen: List[Node]
): (Node, List[Node]) = {
  rest match
    case Nil => (min, seen)
    case c :: xs =>
      if c._2 <= min._2 then getMinAux(c, xs, minTrans(seen, min, c))
      else getMinAux(min, xs, minInv(seen, min, c))
}

// extract min from list
def getMin(l: List[Node]): (Node, List[Node]) = {
  l match
    case h :: Nil => (h, Nil)
    case h :: t   => getMinAux(h, t, Nil)
}

def prepareAux(
    graph: List[(Int, List[Node])],
    start: Int
): List[Node] = {
  graph match
    case Nil => Nil
    case (v, _) :: xs if v == start =>
      (v, Real(0)) :: prepareAux(xs, start)
    case (v, _) :: xs => (v, Inf) :: prepareAux(xs, start)
}

case class Graph(graph: List[(Int, List[(Int, Distance)])]) {

  // direct distance between nodes u -> v
  def distance(u: Int, v: Int): Distance = {
    graph.get(u).flatMap(_.get(v)) match
      case None    => Inf
      case Some(d) => d
  }

  // update distant to node tar (when at bode cur)
  def updateDist(cur: Node, tar: Node): Node = {
    val nd = cur._2 + distance(cur._1, tar._1)
    (tar._1, if nd <= tar._2 then nd else tar._2)
  } ensuring (res => res._2 <= tar._2 && cur._2 <= res._2)

  // update distance from cur
  def iterOnce(cur: Node, rest: List[Node]): List[Node] = {
    rest match {
      case Nil    => Nil
      case h :: t => updateDist(cur, h) :: iterOnce(cur, t)
    }
  }

  def itInv(seen: List[Node]): Boolean =
    seen.forall { case (m, d0) =>
      seen.forall { case (n, d) =>
        n == m ||
        (graph.get(n).flatMap(_.get(m)) match
          case None     => true
          case Some(d1) => d0 <= d1 + d
        )
      }
    }

  // dijkstra main loop
  def iterate(seen: List[Node], future: List[Node]): List[Node] = {
    require(itInv(seen))
    future match
      case Nil => seen
      case fu =>
        val (h, t) = getMin(fu)
        iterate(h :: seen, iterOnce(h, t))
  }

  // init dist queue
  def prepare(start: Int): List[Node] =
    prepareAux(graph, start)

  def dijkstra(start: Int): List[Node] =
    iterate(Nil, prepare(start))

}

val g = Graph(
  List(
    (1, List(2 -> 1.toDist, 3 -> 3.toDist)),
    (2, List(4 -> 5.toDist, 3 -> 1.toDist)),
    (3, List(4 -> 2.toDist)),
    (4, List()),
    (5, List(4 -> 2.toDist))
  )
)

assert(g.distance(1, 2) == Real(BigInt(1)))
assert(g.distance(2, 1) == Inf)
assert(g.prepare(1).get(1) == Some(Real(0)))
assert(g.prepare(1).get(2) == Some(Inf))
assert(getMin(g.prepare(1))._1 == 1 -> Real(0))
assert(getMin(g.prepare(1))._2.forall(_._2 == Inf))
assert(g.iterOnce(1 -> Real(0), g.prepare(1)).get(2) == Some(Real(1)))

g.dijkstra(1)
