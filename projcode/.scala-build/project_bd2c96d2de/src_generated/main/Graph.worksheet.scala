



object `Graph.worksheet` {
/*<script>*/trait Ord[A] {
  extension (self: A)
    def <(that: A): Boolean
    def ===(that: A): Boolean = self == that
    def <=(that: A): Boolean = self === that || self < that
}

type Node = String

enum Distance {
  case R(i: Int)
  case I

  def +(that: Distance): Distance = (this, that) match
    case (_, I)       => I
    case (I, _)       => I
    case (R(i), R(j)) => R(i + j)

  override def toString: String = this match
    case Distance.R(i) => i.toString
    case Distance.I    => "inf"

}

given Ord[Distance] with {
  import Distance._
  extension (self: Distance)
    def <(that: Distance): Boolean = (self, that) match
      case (I, I)       => false
      case (I, R(_))    => false
      case (R(_), I)    => true
      case (R(i), R(j)) => i < j
}

enum Heap[+A] {
  case Empty
  case Vertex(h: A, t: List[Heap[A]])

  def size: Int = this match
    case Empty        => 0
    case Vertex(h, t) => 1 + t.map(_.size).sum
}

object Heap {
  def merge[A: Ord](left: Heap[A], right: Heap[A]): Heap[A] =
    (left, right) match
      case (Empty, h) => h
      case (h, Empty) => h
      case (Vertex(h1, t1), Vertex(h2, t2)) =>
        if h1 < h2 then Vertex(h1, right :: t1) else Vertex(h2, left :: t2)

  def insert[A: Ord](v: A, h: Heap[A]): Heap[A] =
    merge(Vertex(v, Nil), h)

  def insHeap[A: Ord](h: Heap[A], t: List[Heap[A]]): Heap[A] =
    t.foldRight(h)(merge)

  def extractMin[A: Ord](h: Heap[A]): Option[(A, Heap[A])] = h match
    case Empty              => None
    case Vertex(h, Nil)     => Some(h -> Empty)
    case Vertex(h, x :: xs) => Some(h -> insHeap(x, xs))

  def apply[A: Ord](xs: A*): Heap[A] = xs.toList.toHeap

  extension [A: Ord](self: Heap[A]) {
    def toList: List[A] = Heap.extractMin(self) match
      case None         => Nil
      case Some(h -> t) => h :: t.toList

    def forget: List[A] = self match
      case Empty        => Nil
      case Vertex(h, t) => h :: t.flatMap(_.forget)
  }

  extension [A: Ord](self: List[A]) {
    def toHeap: Heap[A] = self.foldRight(Empty: Heap[A])(insert)
  }

}

import Heap.toHeap
def sort[A:Ord](l: List[A]):List[A] = l.toHeap.toList

case class Assoc(n: Node, d: Distance) {
  override def toString: String = s"$n -> $d"
}

given Ord[Int] with {
  extension (self: Int) def <(that: Int): Boolean = self < that
}

given Ord[Assoc] with {
  extension (self: Assoc) def <(that: Assoc): Boolean = self.d < that.d
}

case class Graph(graph: Map[Node, Map[Node, Distance]]) {
  import Heap.toHeap
  import Distance._

  def dijkstra(src: Node): List[Assoc] =
    def go(res: List[Assoc])(q: Heap[Assoc]): List[Assoc] =
      Heap.extractMin(q) match
        case None => res
        case Some((h @ Assoc(nu, du), tl)) =>
          def f(e: Assoc) = graph.get(nu).flatMap(_.get(e.n)) match
            case None    => e
            case Some(w) => Assoc(e.n, if du + w < e.d then du + w else e.d)
          go(h :: res)(tl.forget.map(f).toHeap)

    go(Nil)(
      graph.keys.toList
        .map(n => Assoc(n, if n == src then R(0) else I))
        .toHeap
    )

}

object Graph {
  def ins(xs: List[(Node, Node, Distance)])(
      g: Map[Node, Map[Node, Distance]]
  ): Map[Node, Map[Node, Distance]] =
    xs match
      case Nil => g
      case (u, v, w) :: next =>
        ins(next)(
          g.updatedWith(u) {
            case None    => Some(Map(v -> w))
            case Some(m) => Some(m.updated(v, w))
          }
        )

  def apply(vertices: (Node, Node, Int)*): Graph =
    Graph(
      ins(vertices.map((a, b, c) => (a, b, Distance.R(c))).toList)(Map.empty)
    )
}

val test = Graph(
  ("a", "b", 10),
  ("a", "c", 5),
  ("b", "c", 2),
  ("c", "b", 3),
  ("b", "d", 1),
  ("c", "d", 9),
  ("c", "e", 2),
  ("d", "e", 4),
  ("e", "d", 6),
  ("e", "a", 7)
).dijkstra("a")

sort(List(1, 1, 4, 5, 1, 4, 114514))/*</script>*/ /*<generated>*/
def args = `Graph.worksheet_sc`.args$
  /*</generated>*/
}

object `Graph.worksheet_sc` {
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
    `Graph.worksheet`.hashCode() // hasCode to clear scalac warning about pure expression in statement position
  }
}

