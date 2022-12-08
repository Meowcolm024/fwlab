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

def getMinAux(
    min: Node,
    rest: List[Node],
    seen: List[Node]
): (Node, List[Node]) = {
  rest match
    case Nil() => (min, seen)
    case Cons(c @ (h, v), xs) =>
      if v <= min._2 then getMinAux(c, xs, seen ++ Cons(min, Nil()))
      else getMinAux(min, xs, seen ++ Cons(c, Nil()))
} ensuring (res =>
  res._2.size == rest.size + seen.size &&
    res._2.content ++ Set(res._1) == rest.content ++ seen.content ++ Set(min)
)

def getMin(l: List[Node]): (Node, List[Node]) = {
  require(l != Nil())
  l match
    case Cons(h, Nil()) => (h, Nil())
    case Cons(h, t)     => getMinAux(h, t, Nil[Node]())
} ensuring (res =>
  res._2.size == l.size - 1 &&
    res._2.content ++ Set(res._1) == l.content
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
  graph match
    case Nil() => Nil()
    case Cons((v, _), xs) if v == start =>
      Cons((v, Real(0)), prepareAux(xs, start))
    case Cons((v, _), xs) => Cons((v, Inf), prepareAux(xs, start))
} ensuring (res => prepareProp(res, graph, start))

case class Graph(graph: List[(Int, List[(Int, Distance)])]) {
  require(noDuplicates(graph) && graph.forall(e => noDuplicates(e._2)))

  // distance between nodes
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
      res.zip(rest).forall((y, x) => y._1 == x._1 && y._2 <= x._2)  // updated dists should be smaller
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
    prepareAux(graph, start)
  } ensuring (res => prepareProp(res, graph, start))

  def dijkstra(start: Int): List[Node] = {
    iterate(Nil[Node](), prepare(start))
  }

}

@extern
def main: Unit = {
  val g = Graph(
    Cons(
      (1, Cons((2, Real(BigInt(1))), Cons((3, Real(BigInt(3))), Nil()))),
      Cons(
        (2, Cons((4, Real(BigInt(5))), Cons((3, Real(BigInt(1))), Nil()))),
        Cons((3, Cons((4, Real(BigInt(2))), Nil())), Nil())
      )
    )
  )
  assert(g.distance(1, 2) == Real(BigInt(1)))
  assert(g.distance(2, 1) == Inf)
  println((g.dijkstra(1).get(4) == Some(Real(BigInt(4)))).toString)
}
