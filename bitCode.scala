import scala.annotation.tailrec
import scala.language.implicitConversions
import scala.language.reflectiveCalls
import java.io._

//Bitcode type deffinition
type bit = Int //0 or 1
type BS = List[bit]

//Regular expressions
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
case class STAR(r: Rexp) extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp

//Annotated regular expressions
abstract class RI
case object IZERO extends RI
case class IONE(bs: BS) extends RI
case class ICHAR(bs: BS, c: Char) extends RI
case class IALT(bs: BS, r1: RI, r2: RI) extends RI
case class ISEQ(bs: BS, r1: RI, r2: RI) extends RI
case class ISTAR(bs: BS, r1: RI) extends RI

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

/** Creats a Bit-code sequence for a value
  *
  * @param v the value a bitcode sequence is to be calculated
  * @return a bitsequence equivelent of the given value
  */
def encode(v : Val) : BS = v match {
  case Empty => List()
  case Chr(c) => List()
  case Left(v) => List(0) ++ encode(v)
  case Right(v) => List(1) ++ encode(v)
  case Sequ(v1,v2) => encode(v1) ++ encode(v2)
  case Stars(List())=> List(1)
  case Stars(v::vs) => List(0) ++ encode(v) ++ encode(Stars(vs))
}

/** Creats a value from a given regular expression and its bitcode sequence
  *
  * @param r,bs the regular expression a value is to be calculated.
  * bs the bitcode sequence assosiated to the regular expression.
  * @return a Value of how the regular expression matched a string denoted by the bs
  */
def decode_aux(r: Rexp, bs: BS) : (Val, BS) = (r, bs) match {
  case (ONE, bs) => (Empty, bs)
  case (CHAR(c), bs) => (Chr(c), bs)
  case (ALT(r1, r2), 0::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    (Left(v), bs1)
  }
  case (ALT(r1, r2), 1::bs) => {
    val (v, bs1) = decode_aux(r2, bs)
    (Right(v), bs1)
  }
  case (SEQ(r1, r2), bs) => {
    val (v1, bs1) = decode_aux(r1, bs)
    val (v2, bs2) = decode_aux(r2, bs1)
    (Sequ(v1, v2), bs2)
  }
  case (STAR(r1), 0::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    val (Stars(vs), bs2) = decode_aux(STAR(r1), bs1)
    (Stars(v::vs), bs2)
  }
  case (STAR(_), 1::bs) => (Stars(Nil), bs)
  case (RECD(x, r1), bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    (Rec(x, v), bs1)
  }
}

def decode(r: Rexp, bs: BS) = decode_aux(r, bs) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}


/** Helper method for internalise, addes a bitocde sequence to the start of a
  * annotated regular expression
  *
  * @param bs,r the bitcode sequence to append. The anotated regular expression bs is appended to
  * @return an anotated regular expression where bs is appended to the front of r
  */
def fuse(bs:BS, r: RI) : RI = r match {
  case IZERO => IZERO
  case IONE(p) => IONE(bs++p)
  case ICHAR(p,r1) => ICHAR(bs++p,r1)
  case IALT(p,r1,r2) => IALT(bs++p,r1,r2)
  case ISEQ(p,r1,r2) => ISEQ(bs++p,r1,r2)
  case ISTAR(p,r) => ISTAR(bs++p,r)
}


/** Convertes a regular expression into a annotated regular expression
  *
  * @param r a regular expression to be transformed
  * @return a anotated regular expression of r
  */
def internalise(r: Rexp) : RI = r match {
  case ZERO => IZERO
  case ONE => IONE(Nil)
  case CHAR(c) => ICHAR(Nil,c)
  case ALT(a1,a2) => IALT(Nil,fuse(List(0),internalise(a1)),fuse(List(1),internalise(a2)))
  case SEQ(s1,s2) => ISEQ(Nil,internalise(s1),internalise(s2))
  case STAR(s) => ISTAR(Nil,internalise(s))
  case RECD(x, r) => internalise(r)
}

/** Checks if an anotated regular expressions can match the
  * empty string anotated regular expression.
  *
  * @param r the anotated regular expression to check
  * @return a boolean value for if r matches the empty string regular expression
  */
def nullable (ri: RI) : Boolean = ri match {
  case IZERO => false
  case IONE(bs) => true
  case ICHAR(bs,_) => false
  case IALT(bs,ri1, ri2) => nullable(ri1) || nullable(ri2)
  case ISEQ(bs,ri1, ri2) => nullable(ri1) && nullable(ri2)
  case ISTAR(bs,ri) => true
}

/** Computes an bit-code sequence for how a annotated regular expression matched the empty string .
  *
  * @param r the annotated regular expression a bit-code sequence is to be made
  * @return a bit-code sequence for how r matched the empty string
  */
def mkEpsBC(ri: RI) : BS = ri match {
  case IONE(bs) => bs
  case IALT(bs,ri1,ri2) =>
    if(nullable(ri1)) bs++mkEpsBC(ri1) else bs++mkEpsBC(ri2)
  case ISEQ(bs,ri1,ri2) => bs++mkEpsBC(ri1)++mkEpsBC(ri2)
  case ISTAR(bs,_) => bs++List(1)
}

/** Builds a derivitive annotated regular expression
  *
  * @param c,r r, the regular expression a derivitive will be build for with respect to character c
  * @return a derivitive annotated regular expression
  */
//Somthing not quite right with my IALT statment used in case ISEQ
def Ider(c: Char,ri: RI) : RI = ri match {
  case IZERO => IZERO
  case IONE(bs) => IZERO
  case ICHAR(bs,d) => if(d == c) IONE(bs) else IZERO
  case IALT(bs,ri1,ri2) => IALT(bs,Ider(c,ri1),Ider(c,ri2))
  case ISEQ(bs,ri1,ri2) =>
    if(nullable(ri1)) IALT(bs,ISEQ(Nil /*TODO why not bs*/,Ider(c,ri1),ri2),fuse(mkEpsBC(ri1),Ider(c,ri2)))
    else ISEQ(bs,Ider(c,ri1),ri2)
  case ISTAR(bs,ri) => ISEQ(bs,fuse(List(0),Ider(c,ri)),ISTAR(Nil,ri))
}

/** Iterates the Ider function over a list of characters
  *
  * @param s,r s the list of character to be iterated on r
  * @return a anotated regular expression that matches the empty string
  */
@tailrec
def ders (s: List[Char], r: RI) : RI = s match {
  case Nil => r
  case c::s => ders(s, Ider(c, r))
}

/** calculates a bit-code sequence for how a annotated regular expression matches a string
  *
  * @param r,s the regular expression a bs is to be calculated with respect to s
  * @return a bit-code sequence
  */
def parseBC0(r: RI,s: List[Char]) : BS = s match {
  case Nil => if (nullable(r)) mkEpsBC(r) else throw new Exception("Not matched")
  case c::cs => parseBC0(Ider(c, r), cs)
}

/** calculates a value for how regular expression matches a string
  *
  * dose this by calling auxiliry function parseBC0 and decoding the resulting bitcode bitsequence
  * with the given regular expressions
  *
  * @param r,s the regular expression to match the string s
  * @return a value for how r matched s
  */
def parseBC(r: Rexp, s: String) : Val = decode(r, parseBC0(internalise(r), s.toList))


//Start of the simplification (Not compleated)
def isPhi(r: RI) : Boolean = r match {
  case IZERO => true
  case IONE(bs) => false
  case ICHAR(bs,d) => false
  case IALT(bs,ri1,ri2) => isPhi(ri1) && isPhi(ri2)
  case ISEQ(bs,ri1,ri2) => isPhi(ri1) || isPhi(ri2)
  case ISTAR(bs,ri) => false
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
def size(ri: RI) : Int = ri match {
  case IZERO => 1
  case IONE(_) => 1
  case ICHAR(_,_) => 1
  case IALT(_,r1, r2) => 1 + size(r1) + size(r2)
  case ISEQ(_,r1, r2) => 1 + size(r1) + size(r2)
  case ISTAR(_,r) => 1 + size(r)
}

//helper method to construct a sequence of of alternative regular expressions.
def adder(r: Rexp, i: Int) : Rexp = i match {
  case 1 => r
  case n => r ~ adder(r,i-1)
}



//Tests
//======================


//Observation: even though size is kept small memory overflow occures still
//evil regular expression 0.2
//a**b
//=========================

println("")
println("evil Test 0.2")
println("")
val regex02 = ((("a").%).%)~"b"

//not Simplified
println("not-Simplified")
for (i <- 1 to 18 by 1) {
  var s = size(ders((("a" * i) + "b").toList,internalise(regex02)))
  println(i + ": " + "%.5f".format(time_needed(1, parseBC(regex02, (("a" * i) + "b")))) + "   Size: " + s)
}


//evil regular expression 1
//a**
//=========================

println("")
println("evil Test 1")
println("")
val regex1 = (("a").%).%

//not simplified
println("not-Simplified")
for (i <- 1 to 17 by 1) {
  var s = size(ders(("a" * i).toList,internalise(regex1)))
  println(i + ": " + "%.5f".format(time_needed(1, parseBC(regex1, "a" * i))) + "   Size: " + s)
}


//evil regular expression 2
//a++
//=========================

println("")
println("evil Test 2")
println("")
val regex2 = (("a")~("a").%)~(("a")~("a").%).%

//Not simplified
println("not-Simplified")
for (i <- 1 to 19 by 1) {
  var s = size(ders(("a" * i).toList,internalise(regex2)))
  println(i + ": " + "%.5f".format(time_needed(1, parseBC(regex2, "a" * i))) + "   Size: " + s)
}


//evil regular expression 3
//(a|aa)+
//=========================

println("")
println("evil Test 3")
println("")
val regex3 = ("a" | "aa") ~ ("a" | "aa").%


//not Simplified
println("not-Simplified")
for (i <- 1 to 20 by 1) {
  var s = size(ders(("a" * i).toList,internalise(regex3)))
  println(i + ": " + "%.5f".format(time_needed(1, parseBC(regex3, "a" * i))) + "   Size: " + s)
}
