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

case class Graph(graph: List[(Int, List[(Int, Distance)])]) {}
