import stainless.collection._
import stainless.lang._
import stainless.annotation._

object testHeap {
      /*~~~~~~~~~~~~~~~~~~~~~~~*/
  /* Data type definitions */
  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  case class Node(rank : BigInt, elem : Int, nodes : Heap)

  sealed abstract class Heap
  private case class  Nodes(head : Node, tail : Heap) extends Heap
  private case object Empty extends Heap

  sealed abstract class OptInt
  case class Some(value : Int) extends OptInt
  case object None extends OptInt

  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  /* Abstraction functions */
  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  def heapContent(h : Heap) : Set[Int] = h match {
    case Empty => Set.empty[Int]
    case Nodes(n, ns) => nodeContent(n) ++ heapContent(ns)
  }

  def nodeContent(n : Node) : Set[Int] = n match {
    case Node(_, e, h) => Set(e) ++ heapContent(h)
  }

  /*~~~~~~~~~~~~~~~~~~~~~~~~*/
  /* Helper/local functions */
  /*~~~~~~~~~~~~~~~~~~~~~~~~*/
  private def reverse(h : Heap) : Heap = reverse0(h, Empty)
  private def reverse0(h : Heap, acc : Heap) : Heap = (h match {
    case Empty => acc
    case Nodes(n, ns) => reverse0(ns, Nodes(n, acc))
  }) ensuring(res => heapContent(res) == heapContent(h) ++ heapContent(acc))

  private def link(t1 : Node, t2 : Node) = (t1, t2) match {
    case (Node(r, e1, ns1), Node(_, e2, ns2)) =>
      if(e1 <= e2) {
        Node(r + 1, e1, Nodes(t2, ns1))
      } else {
        Node(r + 1, e2, Nodes(t1, ns2))
      }
  }

  private def insertNode(t : Node, h : Heap) : Heap = (h match {
    case Empty => Nodes(t, Empty)
    case Nodes(t2, h2) =>
      if(t.rank < t2.rank) {
        Nodes(t, h)
      } else {
        insertNode(link(t, t2), h2)
      }
  }) ensuring(res => heapContent(res) == nodeContent(t) ++ heapContent(h))

  private def getMin(h : Heap) : (Node, Heap) = {
    require(h != Empty)
    h match {
      case Nodes(t, Empty) => (t, Empty)
      case Nodes(t, ts) =>
        val (t0, ts0) = getMin(ts)
        if(t.elem < t0.elem) {
          (t, ts)
        } else {
          (t0, Nodes(t, ts0))
        }
    }
  } ensuring(_ match {
    case (n,h2) => nodeContent(n) ++ heapContent(h2) == heapContent(h)
  })

  /*~~~~~~~~~~~~~~~~*/
  /* Heap interface */
  /*~~~~~~~~~~~~~~~~*/
  def empty() : Heap = {
    Empty
  } ensuring(res => heapContent(res) == Set.empty[Int])

  def isEmpty(h : Heap) : Boolean = {
    (h == Empty)
  } ensuring(res => res == (heapContent(h) == Set.empty[Int]))

  def insert(e : Int, h : Heap) : Heap = {
    insertNode(Node(0, e, Empty), h)
  } ensuring(res => heapContent(res) == heapContent(h) ++ Set(e))

  def merge(h1 : Heap, h2 : Heap) : Heap = ((h1,h2) match {
    case (_, Empty) => h1
    case (Empty, _) => h2
    case (Nodes(t1, ts1), Nodes(t2, ts2)) =>
      if(t1.rank < t2.rank) {
        Nodes(t1, merge(ts1, h2))
      } else if(t2.rank < t1.rank) {
        Nodes(t2, merge(h1, ts2))
      } else {
        insertNode(link(t1, t2), merge(ts1, ts2))
      }
  }) ensuring(res => heapContent(res) == heapContent(h1) ++ heapContent(h2))

  def findMin(h : Heap) : OptInt = (h match {
    case Empty => None
    case Nodes(Node(_, e, _), ns) =>
      findMin(ns) match {
        case None => Some(e)
        case Some(e2) => Some(if(e < e2) e else e2)
      }
  }) ensuring(_ match {
    case None => isEmpty(h)
    case Some(v) => heapContent(h).contains(v)
  })

  def deleteMin(h : Heap) : Heap = (h match {
    case Empty => Empty
    case ts : Nodes =>
      val (Node(_, e, ns1), ns2) = getMin(ts)
      merge(reverse(ns1), ns2)
  }) ensuring(res => heapContent(res).subsetOf(heapContent(h)))

  def extractMin(h: Heap) : (Int, Heap) = (h match {
    // = findMin + extractMi
    case Empty => None
    case Nodes(Node(_, e, ns1), ns2) => {
        ????
    }
  })

  def Sort(l0: List[Int]) : List[Int] = {
    val h0 = l0.foldRight(Empty:Heap)((ele, h) => insert(ele, h))

  }

  def sanity1() : Boolean = {
    val h0 = insert(42, Empty)
    val h1 = insert(0, Empty)
    val h2 = merge(h0, h1)
    findMin(h2) == Some(0)
  }.holds
    @extern
  def main(args: Array[String]): Unit = {
      println("2222")
  //   println(subList(List(0, 2), List(0, 1, 2))) // true
  //   println(subList(List(1, 0), List(0, 0, 1))) // false
  //   println(subList(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))) // true
  }

}