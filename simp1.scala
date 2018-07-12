import scala.language.implicitConversions
import scala.language.reflectiveCalls
import java.io._
import scala.io.Source._

//Regular expression
abstract class Rexp
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
case class NOT(r: Rexp) extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp

//Values
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val


//Some convenience for typing in regular expressions
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
  def $ (r: Rexp) = RECD(s, r)
}

/** Checks if a regular expressions can match the
  * empty.
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
  case NOT(r) => !(nullable(r))
  case RECD(_, r1) => nullable(r1)
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
  case NOT(r) => NOT(der(c,r))
  case RECD(_, r1) => der(c, r1)
}

/** Simplification function for the matcher
  *
  * @param r the regular expression to be simplified
  * @return a simplified regular expression
  */
def firstSimp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (firstSimp(r1), firstSimp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (firstSimp(r1), firstSimp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    RECD(x, r1s)
  }
  case r => r
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
  case c::s => simpDers(s, firstSimp(der(c, r)))
}

/** Matches a regular expression to a string
  *
  * @param r,s the regular expression to match the string
  * @return a boolean for if the regular expression can match the string
  **/
def matcher (r: Rexp,s: String) : Boolean = {
  nullable(simpDers(s.toList,r))
}

// rectification functions for simplification
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
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")


/** Simplification for lexing. Makes use of the rectification functions.
  *
  * @param r the regular expression to be Simplified
  * @return a simpified regular expression and a rectification function
  */
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
      else (ALT (r1s, r2s), F_ALT(f1s, f2s))
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
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
  case RECD(x, r) => Rec(x, mkeps(r))

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
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))

  case (NTIMES(r, n), Sequ(v1,Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (CHOICE(s), Empty) => Chr(c)
  case (OPT(r), v) => Left(inj(r,c,v))

  case (NOMORE(r, n), Sequ(v1,Stars(vs))) => Stars(inj(r,c,v1)::vs)
  case (ATLEAST(r, n), Sequ(v1,Stars(vs))) => Stars(inj(r,c,v1)::vs)
  case (ATLEASENOMORE(r, n, m), Sequ(v1,Stars(vs)))=> Stars(inj(r,c,v1)::vs)
}

/** Extracts a string from value.
  *
  * @param v the value a string is to be extracted from
  * @return a string of what the value is representing
  */
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

/** Extracts an environment from a value
  *
  * @param v a value where records need to be extracted
  * @return a list of tokens
  */
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}


/** Main lexing function (produces a value) with no simplification
  *
  * @param r,s  r the regular expression to lex the list of characters s
  * @return a value for how a regular expression matched a string
  */
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r)
  else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}
//implemented for convienence
def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)


/** Main lexing function (produces a value) with simplification
  *
  * @param r,s  r the regular expression to lex the list of characters s
  * @return a value for how a regular expression matched a string
  */
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}
//implemented for convienence
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
  case RECD(_,r) => 1 + size(r)
}

//helper method to construct a sequence of of alternative regular expressions.
def adder(r: Rexp, i: Int) : Rexp = i match {
  case 1 => r
  case n => r ~ adder(r,i-1)
}





// Sulzmann's tests
//==================
/*
println("")
println("Test 1")
println("")
val sulzmann = ("a" | "b" | "ab").%

println(lexing(sulzmann, "a" * 10))
println(lexing_simp(sulzmann, "a" * 10))

for (i <- 1 to 4000 by 500) {
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(sulzmann, "a" * i))))
}

//any higher and run out of memory
//val pw = new PrintWriter(new File("GraphData.txt" ))
for (i <- 1 to 1501 by 500) {
  println(i + ": " + "%.5f".format(time_needed(1, lexing(sulzmann, "a" * i))))
  //pw.write("%.5f".format(time_needed(1, lexing(sulzmann, "a" * i))) + ",")
}
//pw.close

for (i <- 1 to 56 by 5) {
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(sulzmann, "ab" * i))))
}
*/



/*
//Size Tests
//=========================

val EVILRegex = SEQ(STAR(STAR(CHAR('a'))), CHAR('b'))

//not simplified
println(size(ders("".toList, EVILRegex)))
println(size(ders("a".toList, EVILRegex)))
println(size(ders("aa".toList, EVILRegex)))
println(size(ders("aaa".toList, EVILRegex)))
println(size(ders("aaaa".toList, EVILRegex)))
println(size(ders("aaaaa".toList, EVILRegex)))
println(size(ders("aaaaaa".toList, EVILRegex)))

//simplified
println(size(simpDers("".toList, EVILRegex)))
println(size(simpDers("a".toList, EVILRegex)))
println(size(simpDers("aa".toList, EVILRegex)))
println(size(simpDers("aaa".toList, EVILRegex)))
println(size(simpDers("aaaa".toList, EVILRegex)))
println(size(simpDers("aaaaa".toList, EVILRegex)))
println(size(simpDers("aaaaaa".toList, EVILRegex)))
*/


//evil regular expression 0
//a*b
//=========================

println("")
println("a*.b")
println("")
val regex01 = ("a".%) ~ "b"

/*
for (i <- 1 to 100000 by 500) {
  val s = size(simpDers(("a" * i).toList,regex01))
  println(i + ": " + "%.5f".format(time_needed(1, simpDers(("a" * i).toList,regex01 ))) + "   Size: "  + s )
  //println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex01, ("a" * i)+"b"))) + "   Size: " + "ignore")
}
*/

//evil regular expression 0.1
//a?{n}a{n}
//=========================

println("")
println("evil Test 0.1")
println("")


//Not simplified
println("Not simplified")
for (i <- 1 to 10 by 1) {
  //val regex011 = NTIMES(OPT("a"),i) ~ NTIMES("a",i)
  val regex011 = adder(("a"|ONE),i) ~ adder("a",i)

  //Matcher
  val s = size(ders(("a" * i).toList,regex011))
  //println(i + ": " + "%.5f".format(time_needed(1, ders(("a" * i).toList,regex011 ))) + "   Size: "  + s )

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex011, "a" * i))) + "   Size: " + s)
}

//Simplified
println("Simplified")
for (i <- 1 to 19 by 1) {
  //val regex01 = NTIMES(OPT("a"),i) ~ NTIMES("a",i)
  val regex01 = adder(("a"|ONE),i) ~ adder(CHAR('a'),i)

  //Matcher
  val s = size(simpDers(("a" * i).toList,regex01))
  //println(i + ": " + "%.5f".format(time_needed(1, simpDers(("a" * i).toList,regex01 ))) + "   Size: "  + s )

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex01, "a" * i))) + "   Size: " + s)
}



//evil regular expression 0.2
//a**b
//=========================

println("")
println("evil Test 0.2")
println("")
val regex02 = ((("a").%).%)~"b"

//Not simplified
println("Not simplified")
for (i <- 1 to 19 by 1) {

  //Matcher
  val s = size(ders(("a" * i).toList,regex02))
  //println(i + ": " + "%.5f".format(time_needed(1,ders(("a" * i).toList,regex02)))+ "   Size: " + s)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex02, (("a" * i) + "b")))) + "   Size: " + s)

}

//Simplified
println("Simplified")
for (i <- 1 to 20 by 1) {

  //Matcher
  val s = size(simpDers(("a" * i).toList,regex02))
  //println(i + ": " + "%.5f".format(time_needed(1, simpDers(regex02, (("a" * i))))) + "   Size: " + s)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex02, (("a" * i) + "b")))) + "   Size: " + s)
}




//evil regular expression 1
//a**
//=========================

println("")
println("evil Test 1")
println("")
val regex1 = (("a").%).%

//Not simplified
println("Not simplified")
for (i <- 1 to 20 by 1) {

  //Lexer
  val s = size(ders(("a" * i).toList,regex1))
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex1, "a" * i))) + "   Size: " + s)
}

//Simplified
println("Simplified")
for (i <- 1 to 10 by 1) {

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

//Not simplified
println("Not simplified")
for (i <- 1 to 20 by 1) {

  //Lexer
  val s = size(ders(("a" * i).toList,regex2))
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex2, "a" * i))) + "   Size: " + s)
}

//Simplified
println("Simplified")
for (i <- 1 to 2000 by 100) {

  //Lexer
  val s = size(simpDers(("a" * i).toList,regex2))
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex2, "a" * i))) + "   Size: " + s)
}



//evil regular expression 3
//(a|aa)+
//=========================
println("")
println("evil Test 3")
println("")
val regex3 = ("a" | "aa") ~ ("a" | "aa").%

//Not simplified
println("Not simplified")
for (i <- 1 to 20 by 1) {

  //Lexer
  val s = size(ders(("a" * i).toList,regex3))
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex3, "a" * i))) + "   Size: " + s)
}

//Simplified
println("Simplified")
for (i <- 1 to 20 by 10) {

  //Matcher
  val s = size(simpDers(("a" * i).toList,regex3))
  //println(i + ": " + "%.5f".format(time_needed(1,simpDers(("a" * i).toList,regex3)))+ "   Size: " + s)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex3, "a" * i))) + "   Size: " + s)
}



//evil regular expression 4
//(a|a?)+
//=========================

println("")
println("evil Test 4")
println("")
val regex6 = ("a"|("aa"|""))~("a"|("aa"|"")).%

//Not simplified
println("Not simplified")
for (i <- 1 to 25 by 1) {

  //Lexer
  val s = size(ders(("a" * i).toList,regex6))
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex6, "a" * i))) + "   Size: " + s)
}

//Simplified
println("Simplified")
for (i <- 1 to 27 by 1) {

  //Lexer
  val s = size(simpDers(("a" * i).toList,regex6))
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex6, "a" * i))) + "   Size: " + s)
}



//(the following are for comparison between derivitive implementations not bitcode as then implement the extended regular exprestions)
//evil regular expression 5
//=========================

println("")
println("evil Test 5")
println("Compair results with test 2 (same regex but uses extended regular expresstions)")
println("")
val regex4 = PLUS(PLUS("a"))

/*
//Not simplified
println("Not simplified")
for (i <- 1 to 19 by 1) {

  //Lexer
  val s = size(ders(("a" * i).toList,regex4))
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex4, "a" * i))) + "   Size: " + s)
}

//Simplified
println("Simplified")
for (i <- 1 to 20000 by 100) {

  //Lexer
  val s = size(simpDers(("a" * i).toList,regex4))
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex4, "a" * i))) + "   Size: " + s)
}
*/



//evil regular expression 6
//=========================

println("")
println("evil Test 6")
println("Compair results with test 3 (same regex but uses extended regular expresstions)")
println("")
val regex5 = PLUS("a" | "aa")

/*
//Not simplified
println("Not simplified")
for (i <- 1 to 25 by 1) {

  //Lexer
  val s = size(ders(("a" * i).toList,regex5))
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex5, "a" * i))) + "   Size: " + s)
}

//Simplified
println("Simplified")
for (i <- 1 to 27 by 1) {

  //Lexer
  val s = size(simpDers(("a" * i).toList,regex5))
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex5, "a" * i))) + "   Size: " + s)
}
*/

//evil regular expression 7
//=========================

println("")
println("evil Test 7")
println("Compair results with test 4 (same regex but uses extended regular expresstions)")
println("")
val regex7 = PLUS("a"|OPT("a"))

/*
//Not simplified
println("Not simplified")
for (i <- 1 to 2000 by 100) {

  //Matcher
  val s = size(ders(("a" * i).toList,regex7))
  //println(i + ": " + "%.5f".format(time_needed(1, ders(("a" * i).toList,regex7))) + "   Size: " + s)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing(regex7, "a" * i))) + "   Size: " )
}

//Simplified
println("Simplified")
for (i <- 1 to 2000 by 100) {
  //Matcher
  val s = size(simpDers(("a" * i).toList,regex7))
  //println(i + ": " + "%.5f".format(time_needed(1, simpDers(("a" * i).toList,regex7))) + "   Size: " + s)

  //Lexer
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(regex7, "a" * i))) + "   Size: " )
}
*/

// Simple C Lexing rules
//========================================
//http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf


//Lexing rules
val SYM = CHOICE(('a' to 'z').toSet) | CHOICE(('A' to 'Z').toSet)
val DIGIT = CHOICE(('0' to '9').toSet)
//all keywords used in the c langauge
val KEYWORD : Rexp = "auto" | "break" | "case" | "char" | "const" | "continue" | "default" | "do" | "double" | "else" | "enum" | "extern" | "float" |
                    "for" | "goto" | "if" | "inline" | "int" | "long" | "register" | "restrict" | "return" | "short" | "signed" | "sizeof" |
                    "static" | "struct" | "switch" | "typedef" | "union" | "unsigned" | "void" | "volatile" | "while" | "_Alignas" | "_Alignof" |
                    "_Atomic" | "_Bool" | "_Complex" | "_Generic" | "_Imaginary" | "_Noreturn" | "_Static_assert" | "_Thread_local"
//variable rule for the c language
val ID: Rexp = (SYM | "_") ~ (SYM | DIGIT | "_").%
//constants
val INT: Rexp = DIGIT.%
val FLOA: Rexp = DIGIT.% ~ "." ~ DIGIT.%
val STRING: Rexp = "\"" ~ SYM.% ~ "\""

//PUNCTUATORS aka operators
val PUNCTUATORS: Rexp = "[" | "]" | "(" | ")" | "{" | "}" | "." | "->" | "++" | "--" | "&" | "*" | "+" | "-" | "~" |
                        "!" | "/" | "?" | ":" | ";" | "..." | "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "<<=" | ">>=" |
                        "&=" | "^=" | "|=" | "%" | "&&" | "||" | "|" | "^" | "<<" | ">>" | "==" | "!=" | ">" | "<" |
                        ">=" | "<=" | "," | "#" | "##" /*| "<:" | ":>" | "<%" | "%>" | "%:" | "%:%:"*/

val WHITESPACE = PLUS(" " | "\n" | "\t")
//val COMMENT: Rexp = "/*" ~ (SYM | DIGIT | "_" | WHITESPACE | PUNCTUATORS).% ~ "*/"

val C_REGS = (("k" $ KEYWORD) |
  //("com" $ COMMENT) |
  ("id" $ ID) |
  ("o" $  PUNCTUATORS) |
  ("float" $ FLOA) |
  ("int" $ INT) |
  ("str" $ STRING) |
  ("w" $ WHITESPACE)).%

//program in C
val prog2 = """
int main()
{
  int n, first = 0, second = 1, next, c
  n = 5
  for( c = 0; c < n; c += 1)
  {
    if( c <= 1)
    {
      next = c;
    }
    else
    {
      next = first + second;
      first = second;
      second = next;
    }
    printf(next)
  }
  return 0;
}
"""


println("Tokens For Prog2")
//println(env(lexing_simp(C_REGS, prog2)))
println(env(lexing_simp(C_REGS, prog2)).filterNot{_._1 == "w"}.mkString("\n"))


//Lexing the set of C programs from the glibc libary
var compleat = 0
var fail = 0

def lexfile(s: File) {
  try {
    val prog3 = fromFile(s.toString).mkString
    println(s.toString)
    env(lexing_simp(C_REGS, prog3))
    compleat=compleat+1
  } catch {
    case _ : Throwable => fail = fail + 1
  }
}

//println(time_needed(1,new File("glibc/posix/").listFiles.filter(_.getName.endsWith("c")).foreach(lexfile)))
//println(compleat + " " + fail)



// Two Simple Tests for the While Language
//========================================
// Lexing Rules

/*
val SYM = CHOICE(('a' to 'z').toSet)
val DIGIT = CHOICE(('0' to '9').toSet)
val ID = SYM ~ (SYM | DIGIT).%
val NUM = "0" | SEQ(CHOICE(('1' to '9').toSet),STAR(DIGIT))
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "true" | "false"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val BEGIN: Rexp = "{"
val END: Rexp = "}"
val STRING: Rexp = "\"" ~ SYM.% ~ "\""

val WHILE_REGS = (("k" $ KEYWORD) |
  ("i" $ ID) |
  ("o" $ OP) |
  ("n" $ NUM) |
  ("s" $ SEMI) |
  ("str" $ STRING) |
  ("p" $ (LPAREN | RPAREN)) |
  ("b" $ (BEGIN | END)) |
  ("w" $ WHITESPACE)).%

val v = "if33 ifif then then23 else else 32"
println((lexing_simp(WHILE_REGS, v)))


println("prog0 test")

val prog0 = """read n"""
println(env(lexing(WHILE_REGS, prog0)))
println(env(lexing_simp(WHILE_REGS, prog0)))

println("prog1 test")

val prog1 = """read  n; write (n)"""
println(env(lexing(WHILE_REGS, prog1)))
println(env(lexing_simp(WHILE_REGS, prog1)))
*/
