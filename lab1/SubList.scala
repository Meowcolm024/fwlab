import stainless.collection._
import stainless.lang._
import stainless.annotation._
 
object SubList {
 
  def subList[T](l1: List[T], l2: List[T]): Boolean = (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && subList(xs, ys)) || subList(l1, ys)
  }
 
  def subListRefl[T](l: List[T]): Unit = {
    l match {
      case Nil() => ()
      case Cons(x, xs) => subListRefl(xs)
    }
  }.ensuring(_ =>
    subList(l, l)
  )

  def subListTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subList(l1, l2))
    l1 match {
      case Cons(x, xs) => l2 match {
        case Cons(y, ys) => xs match {
          case Nil() => ()
          case Cons(_, _) => 
            if subList(l1, ys) 
              then subListTail(l1, ys)
              else subListTail(xs, ys)
        }
      }
    }
  }.ensuring(_ =>
    subList(l1.tail, l2)
  )
 
  def subListTails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && subList(l1, l2))
    val Cons(a, l) = l1
    val Cons(b, r) = l2
    l match {
      case Nil() => ()
      case Cons(x, xs) => r match {
        case Cons(y, ys) =>
          if x == y && subList(xs, ys)
            then subListTails(l, r)
            else subListTails(l1, Cons(b, ys))
      }
    }
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )
 
  def subListTrans[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l3))
    l3 match {
      case Nil() => ()
      case Cons(x, xs) => l2 match {
        case Nil() => ()
        case Cons(y, ys) => l1 match {
          case Nil() => ()
          case Cons(z, zs) => 
            if subList(l2, xs)
              then subListTrans(l1, l2, xs)
              else if subList(l1, ys)
                then subListTrans(l1, ys, l3)
                else subListTrans(zs, ys, l3)
        }
      }
    }
  }.ensuring(_ =>
    subList(l1, l3)
  )
 
  def subListLength[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2))
    l1 match {
      case Nil() => ()
      case Cons(x, xs) => l2 match {
        case Cons(y, ys) => 
          if subList(l1, ys)
            then subListLength(l1, ys)
            else subListLength(xs, ys)
      }
    }
  }.ensuring(_ =>
    l1.length <= l2.length
  )
 
  def subListEqual[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && l1.length >= l2.length)
    subListLength(l1, l2)
    (l1, l2) match {
      case (Nil(), Nil()) => ()
      case (Cons(x, xs), Cons(y, ys)) => subListEqual(xs, ys)
    }
  }.ensuring(_ =>
    l1 == l2
  )
 
  def subListAntisym[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l1))
    subListLength(l1, l2)
    subListLength(l2, l1)
    subListEqual(l1, l2)
  }.ensuring(_ =>
    l1 == l2
  )

  def subListAppend[T](l1: List[T], l2: List[T]): Unit ={
    l1 match {
      case Nil() => ()
      case Cons(x, xs) => subListAppend(xs, l2)
    }
  }.ensuring(_ => 
    subList(l1, l1 ++ l2)  
  )

  def subListPrepend[T](l1: List[T], l2: List[T]): Unit = {
    l1 match {
      case Nil() => subListRefl(l2)
      case Cons(x, xs) => l2 match {
        case Nil() => ()
        case Cons(y, ys) => subListPrepend(xs, l2)
      }
    }
  }.ensuring(_ => 
    subList(l2, l1 ++ l2)  
  )

  def subListConcatLeft[T](l: List[T], l1: List[T], l2: List[T]): Unit = {
    require(subList(l, l2))
    l1 match {
      case Nil() => ()
      case Cons(x, xs) => subListConcatLeft(l, xs, l2)
    }
  }.ensuring(_ =>
    subList(l1 ++ l, l1 ++ l2)  
  )

  def subListConcatRight[T](l: List[T], l1: List[T], l2: List[T]): Unit = {
    require(subList(l, l1))
    l match {
      case Nil() => subListPrepend(l1, l2)
      case Cons(x, xs) => l1 match {
        case Cons(y, ys) =>
          if subList(l, ys)
            then subListConcatRight(l, ys, l2)
            else subListConcatRight(xs, ys, l2)
      }
    }
  }.ensuring(_ =>
    subList(l ++ l2, l1 ++ l2)  
  )
 
  @extern
  def main(args: Array[String]): Unit = {
    println(subList(List(0, 2), List(0, 1, 2))) // true
    println(subList(List(1, 0), List(0, 0, 1))) // false
    println(subList(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))) // true
  }
 
}
