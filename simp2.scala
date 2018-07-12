import scala.language.implicitConversions
import scala.language.reflectiveCalls

//Regular expressions
sealed abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
case class STAR(r: Rexp) extends Rexp
case class CHOICE(s: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPT(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
case class NOMORE(r: Rexp, n: Int) extends Rexp
case class ATLEAST(r: Rexp, n: Int) extends Rexp
case class ATLEASENOMORE(r: Rexp, n: Int, m: Int) extends Rexp
//case class NOT(r: Rexp) extends Rexp

//Values
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val


// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
}


/** Checks if a regular expressions can match the
  * empty string.
  *
  * @param r the regular expression to check
  * @return a boolean value for if r matches the empty string
  */
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case CHOICE(s) => false
  case PLUS(r) => nullable(r)
  case OPT(r) =>  true
  case NTIMES(r, n) => if (n == 0) true else nullable(r)
  case NOMORE(r, n) => true
  case ATLEAST(r, n) => if (n == 0) true else nullable(r)
  case ATLEASENOMORE(r, n, m) => if (n == 0) true else nullable(r)
  //case NOT(r) => !(nullable(r))
}

/** Builds a derivitive regular expression
  *
  * @param c,r the regular expression a derivitive will be build for with respect to character
  * @return a derivitive regular expression
  */
def der (c: Char,r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if(c == d) { ONE } else { ZERO }
  case ALT(r1, r2) => ALT(der(c,r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case CHOICE(s) => if(s.contains(c)) ONE else ZERO
  case PLUS(r) => SEQ(der(c,r),STAR(r))
  case OPT(r) => der(c,r)
  case NTIMES(r, n) =>
    if (n == 0) ZERO else SEQ(der(c, r), NTIMES(r, n - 1))
  case NOMORE(r, n) =>
    if(n == 0) ZERO else SEQ(der(c, r), NOMORE(r, n - 1))
  case ATLEAST(r, n) =>
    if(n == 0) SEQ(der(c,r),STAR(r)) else {SEQ(der(c,r),ATLEAST(r,(n-1)))}
  case ATLEASENOMORE(r, n, m) =>
    if(m <= 0) ZERO
    else if(n == 0) SEQ(der(c,r),ATLEASENOMORE(r,n,m-1))
    else SEQ(der(c,r),ATLEASENOMORE(r,n-1,m-1))
  //case NOT(r) => NOT(der(c,r))
}

/** Simplification function for the matcher
  *
  * @param r the regular expression to be simplified
  * @return a simplified regular expression
  */
def firstsimp(r: Rexp, seen: Set[Rexp]): (Rexp, Set[Rexp]) = r match {
  case ALT(r1, r2) => {
    val (r1s, seen1) = firstsimp(r1, seen)
    val (r2s, seen2) = firstsimp(r2, seen1)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, seen2)
      case (_, ZERO) => (r1s, seen2)
      case _ => (ALT (r1s, r2s), seen2)
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, _) = firstsimp(r1, Set())
    val (r2s, _) = firstsimp(r2, Set())
    if (seen.contains(SEQ(r1s, r2s))) (ZERO, seen)
    else (r1s, r2s) match {
      case (ZERO, _) => (ZERO, seen)
      case (_, ZERO) => (ZERO, seen)
      case (ONE, _) => (r2s, seen + r2s)
      case (_, ONE) => (r1s, seen + r1s)
      case _ => (SEQ(r1s,r2s), seen + SEQ(r1s, r2s))
    }
  }
  case r => if (seen.contains(r)) (ZERO, seen) else (r, seen + r)
}

/** Iterates the der function over a list of characters
  *
  * @param s,r s the list of character to be iterated on r
  * @return a regular expression that matches the empty string
  */
def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

/** Iterates the der function over a list of characters
  * simplifying the derivitive at every step
  *
  * @param s,r s the list of character to be iterated on r
  * @return a regular expression that matches the empty string
  */
def simpDers (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => simpDers(s, firstsimp(der(c, r),Set())._1)
}

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) =
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) =
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification of regular expressions returning also an
// rectification function; no simplification under STAR
// - uses a "seen" argument to filter out duplicates in nested ALTs
def simp(r: Rexp, seen: Set[Rexp]): (Rexp, Set[Rexp], Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, seen1, f1s) = simp(r1, seen)
    val (r2s, seen2, f2s) = simp(r2, seen1)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, seen2, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, seen2, F_LEFT(f1s))
      case _ => (ALT (r1s, r2s), seen2, F_ALT(f1s, f2s))
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, _, f1s) = simp(r1, Set())
    val (r2s, _, f2s) = simp(r2, Set())
    if (seen.contains(SEQ(r1s, r2s))) (ZERO, seen, F_ERROR)
    else (r1s, r2s) match {
      case (ZERO, _) => (ZERO, seen, F_ERROR)
      case (_, ZERO) => (ZERO, seen, F_ERROR)
      case (ONE, _) => (r2s, seen + r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, seen + r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), seen + SEQ(r1s, r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => if (seen.contains(r)) (ZERO, seen, F_ERROR) else (r, seen + r, F_ID)
}

/**computes an empty parse tree assuming that r is nullable.
  *
  * @param r a regular expression that matches the empty string
  * @return a value for how r matched the empty string
  */
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) =>
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)

  case PLUS(r) => Stars(List(mkeps(r)))
  case OPT(r) => mkeps(ALT(ONE,r))
  case NTIMES(r, n) => Stars((for(g <- 0 until n) yield mkeps(r)).toList)

  case NOMORE(r, n) => Stars(Nil)
  case ATLEAST(r, n) => Stars((for(g <- 0 until n) yield mkeps(r)).toList)
  case ATLEASENOMORE(r, n, m) => Stars((for(g <- 0 until n) yield mkeps(r)).toList)
}

/** Builds a value for how a regular expression matched a give character.
  *
  * @param r,c,v the regular expression a value is to be calulated, with respect to
  * the character c and prior value v
  * @return a value for how r matched c
  */
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (CHAR(d), Empty) => Chr(c)
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))

  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)

  case (NTIMES(r, n), Sequ(v1,Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (CHOICE(s), Empty) => Chr(c)
  case (OPT(r), v) => Left(inj(r,c,v))

  case (NOMORE(r, n), Sequ(v1,Stars(vs))) => Stars(inj(r,c,v1)::vs)
  case (ATLEAST(r, n), Sequ(v1,Stars(vs))) => Stars(inj(r,c,v1)::vs)
  case (ATLEASENOMORE(r, n, m), Sequ(v1,Stars(vs)))=> Stars(inj(r,c,v1)::vs)
}

// main lexing function (produces a value)
// - no simplification
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r)
              else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}
//Implemented for convienence
def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)



// main lexing function (produces a value)
// - Simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => {
    val (r_simp, _, f_simp) = simp(der(c, r), Set())
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}
//Implemented for convienence
def lexing_simp(r: Rexp, s: String) : Val = lex_simp(r, s.toList)



//Fuctions to help with testing
//===============================

//calculates the time it takes a given function to run
def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}

//calculates the size of the derivitive regular expressions
def size(r: Rexp) : Int = r match {
  case ZERO => 1
  case ONE => 1
  case CHAR(_) => 1
  case ALT(r1, r2) => 1 + size(r1) + size(r2)
  case SEQ(r1, r2) => 1 + size(r1) + size(r2)
  case STAR(r) => 1 + size(r)
  case NTIMES(r, _) => 1 + size(r)
  case CHOICE(_) => 1
  case PLUS(r) => 1 + size(r)
  case OPT(r) => 1 + size(r)
  case NOMORE(r,_) => 1 + size(r)
  case ATLEAST(r,_) => 1 + size(r)
  case ATLEASENOMORE(r,_,_) => 1 + size(r)
  //case NOT(r) => 1 + size(r)
}

//helper method to construct a sequence of of alternative regular expressions.
def adder(r: Rexp, i: Int) : Rexp = i match {
  case 1 => r
  case n => r ~ adder(r,i-1)
}






//Testing
//===============================
//No unsimplified tests.
//Look at Derivitive.scala for corosponding unsimplified tests


//evil regular expression 0
//a*b
//=========================

println("")
println("a*.b")
println("")
val regex01 = ("a".%) ~ "b"

for (i <- 1 to 1000 by 100) {

  //Matcher
  val t = size(simpDers(("a" * i).toList,regex01))
  //println(i + ": " + "%.5f".format(time_needed(1,simpDers(("a" * i).toList,regex01)))+ "   Size: " + t)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex01, ("a" * i)+"b"))) + "   Size: " + t)
}


//evil regular expression 0.1
//(a?){n}a{n}
//=========================

println("")
println("evil Test 0.1")
println("")

for (i <- 1 to 10 by 1) {
  //val regex011 = NTIMES(OPT("a"),i) ~ NTIMES("a",i)
  val regex011 = adder(("a"|ONE),i) ~ adder("a",i)

  //Matcher
  val t = size(simpDers(("a" * i).toList,regex011))
  //println(i + ": " + "%.5f".format(time_needed(1,simpDers(("a" * i).toList,regex011)))+ "   Size: " + t)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex011, "a" * i)))+ "   Size: " + t)
}


//evil regular expression 0.2
//a**b
//=========================

println("")
println("evil Test 0.2")
println("")
val regex02 = ((("a").%).%)~"b"

for (i <- 1 to 20 by 1) {

  //Matcher
  val t = size(simpDers((("a" * i)+"b").toList,regex02))
  //println(i + ": " + "%.5f".format(time_needed(1,simpDers(regex02,(("a" * i)+"b"))))+ "   Size: " + t)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1,lexing_simp(regex02,(("a" * i)+"b"))))+ "   Size: " + t)

}



//evil regular expression 1
//a**
//=========================

println("")
println("evil Test 1")
println("")
val regex1 = (("a").%).%


for (i <- 1 to 1000 by 100) {

  //Lexer
  val s = size(simpDers(("a" * i).toList,regex1))
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex1, "a" * i))) + "   Size: " + s)
}


//evil regular expression 2
//a++
//=========================

println("")
println("evil Test 2")
println("")
val regex2 = (("a")~("a").%)~(("a")~("a").%).%

for (i <- 1 to 1000 by 100) {

  //Lexer
  val s = size(simpDers(("a" * i).toList,regex2))
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex2, "a" * i))) + "   Size: " + s)
}


//evil regular expression 3
//(a|aa)+
//=========================
//answer to question in derivitive for test 3

println("")
println("evil Test 3")
println("")
val regex3 = ("a" | "aa") ~ ("a" | "aa").%

for (i <- 1 to 1000 by 100) {

  //Matcher
  val t = size(simpDers(("a" * i).toList,regex3))
  //println(i + ": " + "%.5f".format(time_needed(1,simpDers(("a" * i).toList,regex3)))+ "   Size: " + t)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex3, "a" * i))) + "   Size: " + t)
}
