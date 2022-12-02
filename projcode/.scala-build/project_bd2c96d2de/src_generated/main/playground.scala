



object playground {
/*<script>*/def add(a: BigInt, b:BigInt):BigInt = {
    require(a >= 0)
    require(b >= 0)
    a + b
    0
} ensuring (res => res >= 0 )/*</script>*/ /*<generated>*/
def args = playground_sc.args$
  /*</generated>*/
}

object playground_sc {
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
    playground.hashCode() // hasCode to clear scalac warning about pure expression in statement position
  }
}

