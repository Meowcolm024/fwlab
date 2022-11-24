trait Ord[A] {
  extension (self: A)
    def ===(that: A): Boolean
    def <(that: A): Boolean
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
}

given Ord[Distance] with {
  import Distance._
  extension (self: Distance)
    def ===(that: Distance) = self == that
    def <(that: Distance): Boolean = (self, that) match
      case (I, I)       => true
      case (I, R(_))    => false
      case (R(_), I)    => true
      case (R(i), R(j)) => i <= j
}

enum Heap[+A] {
  case Empty
  case Vertex(h: A, t: List[Heap[A]])
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

  def apply[A: Ord](xs: A*): Heap[A] =
    xs.toList.foldRight(Empty: Heap[A])(insert)

  def fromList[A: Ord](xs: List[A]): Heap[A] =
    xs.foldRight(Empty: Heap[A])(insert)

  extension [A: Ord](self: Heap[A]) {
    def toList: List[A] = Heap.extractMin(self) match
      case None         => Nil
      case Some(h -> t) => h :: t.toList

    def forget: List[A] = self match
      case Empty        => Nil
      case Vertex(h, t) => h :: t.flatMap(_.forget)
  }
}

case class Graph(graph: Map[Node, Map[Node, Distance]]) {
  def dijkstra = ???
}
