import stainless.annotation._
import stainless.lang._
import stainless.collection._

def add(a: BigInt, b:BigInt):BigInt = {
    require(a >= 0)
    require(b >= 0)
    a + b
} ensuring (res => res >= 0 )

def isSorted(l0: List[Int], cmp: (Int, Int) => Boolean): Boolean = {
  decreases(l0)
  l0 match {
    case Nil()          => true
    case Cons(x, Nil()) => true
    case Cons(x, xs)    => cmp(x, xs.head) && isSorted(xs, cmp)
  } 
}

def test_isSorted(): Boolean = {
    val l = List(1, 2, 3)
    isSorted(l, ((a, b) => a < b))
}.holds

def test_implicit(): Boolean = {
  val c = ((a: BigInt, b: BigInt) => (a + b)).apply(1, 2)
  c == 3
}.holds