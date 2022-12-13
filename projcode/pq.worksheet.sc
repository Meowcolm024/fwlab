import stainless.collection._
import stainless.lang._
import stainless.annotation._

sealed abstract class Distance
case object Inf extends Distance
case class Real(i: BigInt) extends Distance { require(i >= 0) }

extension (i: BigInt) {
  def toDist: Distance =
    require(i >= 0)
    Real(i)
}

extension (self: Distance) {
  def <=(that: Distance): Boolean = (self, that) match
    case (Inf, Inf)         => true
    case (Real(_), Inf)     => true
    case (Inf, Real(_))     => false
    case (Real(l), Real(r)) => l <= r

  def +(that: Distance): Distance = (self, that) match
    case (Real(l), Real(r)) => Real(l + r)
    case _                  => Inf
}

def noDuplicates[A](l: List[(Int, A)]): Boolean = l match {
  case Nil()            => true
  case Cons((k, v), xs) => (xs.get(k) == None[A]()) && noDuplicates(xs)
}

extension [A](self: List[(Int, A)]) {
  def update(x: (Int, A)): List[(Int, A)] = {
    require(noDuplicates(self))
    self match
      case Nil()                        => Nil()
      case Cons((i, v), t) if i == x._1 => Cons((i, x._2), t)
      case Cons(h, t)                   => Cons(h, t.update(x))
  } ensuring (res =>
    res.map(_._1) == self.map(_._1) &&
      res.size == self.size &&
      (res.get(x._1) match
        case Some(v) => v == x._2
        case None()  => res == self
      )
  )

  def get(i: Int): Option[A] = self match
    case Nil()           => None()
    case Cons((h, v), t) => if h == i then Some(v) else t.get(i)
}

type Node = (Int, Distance)

def minTrans(l: List[Node], m: Node, n: Node): List[Node] = {
  require(l.forall(z => m._2 <= z._2) && n._2 <= m._2)
  l match
    case Nil()      => Cons(m, Nil())
    case Cons(h, t) => Cons(h, minTrans(t, m, n))
} ensuring (res =>
  res.size == l.size + 1 &&
    res.content == l.content ++ Set(m) &&
    res.forall(z => n._2 <= z._2)
)

def minInv(l: List[Node], m: Node, n: Node): List[Node] = {
  require(l.forall(z => m._2 <= z._2) && m._2 <= n._2)
  l match
    case Nil()      => Cons(n, Nil())
    case Cons(h, t) => Cons(h, minInv(t, m, n))
} ensuring (res =>
  res.size == l.size + 1 &&
    res.content == l.content ++ Set(n) &&
    res.forall(z => m._2 <= z._2)
)

def getMinAux(
    min: Node,
    rest: List[Node],
    seen: List[Node]
): (Node, List[Node]) = {
  decreases(rest.size)
  require(seen.forall(n => min._2 <= n._2))
  rest match
    case Nil() => (min, seen)
    case Cons(c, xs) =>
      if c._2 <= min._2 then getMinAux(c, xs, minTrans(seen, min, c))
      else getMinAux(min, xs, minInv(seen, min, c))
} ensuring (res =>
  res._2.size == rest.size + seen.size &&
    res._2.content ++ Set(res._1) == rest.content ++ seen.content ++ Set(min) &&
    res._2.forall(n => res._1._2 <= n._2)
)

// extract min from list
def getMin(l: List[Node]): (Node, List[Node]) = {
  require(l != Nil())
  l match
    case Cons(h, Nil()) => (h, Nil())
    case Cons(h, t)     => getMinAux(h, t, Nil[Node]())
} ensuring (res =>
  res._2.size == l.size - 1 &&
    res._2.content ++ Set(res._1) == l.content &&
    res._2.forall(n => res._1._2 <= n._2)
)

def prepareProp(
    res: List[Node],
    graph: List[(Int, List[Node])],
    start: Int
): Boolean =
  res.size == graph.size &&
    res.map(_._1) == graph.map(_._1) &&
    (res.get(start) match {
      case Some(d) => d == Real(0)
      case None()  => res.forall(_._2 == Inf)
    })

def prepareAux(
    graph: List[(Int, List[Node])],
    start: Int
): List[Node] = {
  require(noDuplicates(graph))
  graph match
    case Nil() => Nil()
    case Cons((v, _), xs) if v == start =>
      Cons((v, Real(0)), prepareAux(xs, start))
    case Cons((v, _), xs) => Cons((v, Inf), prepareAux(xs, start))
} ensuring (res => prepareProp(res, graph, start))

def validGraph(graph: List[(Int, List[(Int, Distance)])]): Boolean =
  noDuplicates(graph) &&
    graph.forall(e => noDuplicates(e._2)) &&
    graph.forall((n, a) => a.forall((i, _) => graph.get(i) != None()))

case class Graph(graph: List[(Int, List[(Int, Distance)])]) {
  require(validGraph(graph))

  // direct distance between nodes u -> v
  def distance(u: Int, v: Int): Distance = {
    graph.get(u).flatMap(_.get(v)) match
      case None()  => Inf
      case Some(d) => d
  }

  // update distant to node tar (when at bode cur)
  def updateDist(cur: Node, tar: Node): Node = {
    val nd = cur._2 + distance(cur._1, tar._1)
    (tar._1, if nd <= tar._2 then nd else tar._2)
  } ensuring (_._2 <= tar._2)

  // update distance from cur
  def iterOnce(cur: Node, rest: List[Node]): List[Node] = {
    decreases(rest.size)
    rest match {
      case Nil()      => Nil()
      case Cons(h, t) => Cons(updateDist(cur, h), iterOnce(cur, t))
    }
  } ensuring (res =>
    res.size == rest.size &&
      res
        .zip(rest)
        .forall((y, x) =>
          y._1 == x._1 && y._2 <= x._2
        ) // updated dists should be smaller
  )

  // dijkstra main loop
  def iterate(seen: List[Node], future: List[Node]): List[Node] = {
    decreases(future.size)
    future match
      case Nil() => seen
      case fu @ Cons(_, _) =>
        val (h, t) = getMin(fu)
        iterate(h :: seen, iterOnce(h, t))
  } ensuring (res => res.size == seen.size + future.size)

  // init dist queue
  def prepare(start: Int): List[Node] = {
    require(graph.get(start) != None())
    prepareAux(graph, start)
  } ensuring (res => prepareProp(res, graph, start))

  def dijkstra(start: Int): List[Node] = {
    require(graph.get(start) != None())
    iterate(Nil[Node](), prepare(start))
  }

}

// @extern
def main: Unit = {
  val g = Graph(
    List(
      (1, List(2 -> 1.toDist, 3 -> 3.toDist)),
      (2, List(4 -> 5.toDist, 3 -> 1.toDist)),
      (3, List(4 -> 2.toDist)),
      (4, List())
    )
  )
  assert(g.distance(1, 2) == Real(BigInt(1)))
  assert(g.distance(2, 1) == Inf)
  assert(g.prepare(1).get(1) == Some(Real(0)))
  assert(g.prepare(1).get(2) == Some(Inf))
  assert(getMin(g.prepare(1))._1 == 1 -> Real(0))
  assert(getMin(g.prepare(1))._2.forall(_._2 == Inf))
  assert(g.iterOnce(1 -> Real(0), g.prepare(1)).get(2) == Some(Real(1)))
}
