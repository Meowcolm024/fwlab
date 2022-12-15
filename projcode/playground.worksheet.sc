def decreases[A](a: A): Unit = ()

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
  
  def <=(that: Distance): Boolean = self < that || self == that
  
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

  val edges = graph.flatMap(
    (ve:(Int, List[(Int, Distance)])) 
      => {ve._2.map((e:(Int, Distance)) => (ve._1, e._1, e._2))})
  
  val edges2 = noEmpty(edges.groupBy(_._2), graph)
  
  def noEmpty(edge: Map[Int, List[Tuple3[Int, Int, Distance]]], graph: List[(Int, List[(Int, Distance)])]): 
    Map[Int, List[Tuple3[Int, Int, Distance]]] = {
      graph match {
        case Nil => edge
        case h::t => {
          val res = noEmpty(edge, t)
          if res.contains(h._1) then res else (res + (h._1 -> Nil))
        }
      }
  }
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

  // return value: (Boolean, Boolean) = (Equal, Lessthan)
  def checkNodeIte(seen: List[Node], to: Int, rest_from: List[(Int, Int, Distance)]): (Boolean, Boolean) = {
    decreases(rest_from.size)
    rest_from match
      case Nil => (if to == sourceNode then true else false, true)
      case h::t => {
        val res = checkNodeIte(seen, to, t)
        val Some(cur_dis, _) = seen.get(to)
        val isVisited = seen.get(h._1)
        val cur = isVisited match {
          case None => (false, true)
          case Some(par_dis, _) =>
            (cur_dis == par_dis + h._3, cur_dis <= par_dis + h._3)
        }
        (res._1 || cur._1, res._2 && cur._2)
        //val cur = if from == h._1 then dis.get(to) == dis.get(from) + h._3
      }
  }

  // dijkstra main loop
  def iterate(seen: List[Node], future: List[Node]): List[Node] = {
    decreases(future.size)
    future match
      case Nil => seen
      case fu @ (_ :: _) =>
        val (h, t) = getMin(fu)
        val checkCur = checkNodeIte(h::seen, h._1, edges2(h._1))
        assert(checkCur._1 && checkCur._2)
        iterate(h :: seen, iterOnce(h, t))
  } ensuring (res => res.size == seen.size + future.size)

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

val sourceNode = 2

val (h, t) = getMin(g.prepare(sourceNode))

g.iterOnce(h, t)

g.dijkstra(sourceNode).get(4)

//==== checker ====
val dis = g.dijkstra(sourceNode).sortBy(x => x._1)

dis(2)

val graph = 
  List(
    (1, List(2 -> 1.toDist, 3 -> 3.toDist)),
    (2, List(4 -> 5.toDist, 3 -> 1.toDist)),
    (3, List(4 -> 2.toDist)),
    (4, Nil),
    (5, List(4 -> 2.toDist))
  )

// edge:(Int, Int, Distance) = (from, to, length)
val edges = graph.flatMap(
  (ve:(Int, List[(Int, Distance)])) 
    => {ve._2.map((e:(Int, Distance)) => (ve._1, e._1, e._2))})

val edges2 = noEmpty(edges.groupBy(_._2), graph)

def noEmpty(edge: Map[Int, List[Tuple3[Int, Int, Distance]]], graph: List[(Int, List[(Int, Distance)])]): 
  Map[Int, List[Tuple3[Int, Int, Distance]]] = {
    graph match {
      case Nil => edge
      case h::t => {
        val res = noEmpty(edge, t)
        if res.contains(h._1) then res else (res + (h._1 -> Nil))
      }
    }
}

edges2(1)
edges2(2)
edges2(3)
edges2(4)
edges2(5)

def checkEqual(des: Int, rest: List[(Int, Int, Distance)]): Boolean = {
  rest match {
    case Nil => false
    case h::t => {
      checkEqual(des, t) || dis(des)._2 == dis(h._1)._2 + h._3
    }
  }
}

def checkLess(des: Int, rest: List[(Int, Int, Distance)]): Boolean = {
  rest match {
    case Nil => true
    case h::t => {
      checkLess(des, t) && dis(des)._2 <= dis(h._1)._2 + h._3
    }
  }
}

def checkNode(des: Int, rest: List[(Int, Int, Distance)]): (Boolean, Boolean) = {
  //decreases(rest.size)
  rest match {
    case Nil => (if (dis(des - 1)._2 == Inf || des == sourceNode) then true else false, true)
    //case Nil => (false, true)
    case h::t => {
      val res = checkNode(des, t)
      val res1 = (res._1 || (dis(des - 1)._2 == dis(h._1 - 1)._2 + h._3))
      val res2 = (res._2 && (dis(des - 1)._2 <= dis(h._1 - 1)._2 + h._3))
      (res1, res2)
    }
  }
}

checkNode(2, edges2(2))

def checkGraph(graph: List[(Int, List[(Int, Distance)])]): (Boolean, Boolean) = {
  graph match {
    case Nil => (true, true)
    case h::t => {
      val res = checkGraph(t)
      //assert(res._1 && res._2)
      val cur = checkNode(h._1, edges2(h._1))
      //(res._1 && (cur._1 || edges2(h._1) == Nil), res._2 && cur._2)
      (res._1 && cur._1, res._2 && cur._2)
    }
  }
}

checkNode(1, edges2(1))
checkNode(2, edges2(2))
checkNode(3, edges2(3))
checkNode(4, edges2(4))
checkNode(5, edges2(5))
checkGraph(graph)
