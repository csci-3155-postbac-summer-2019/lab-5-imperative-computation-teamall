package jsy.student

import jsy.lab5.Lab5Like
import jsy.lab5.ast._
import jsy.lab5.Parser.parse
import jsy.tester.JavascriptyTester
import jsy.util.DoWith
import jsy.util.DoWith._
import org.scalatest._

class Lab5Spec(lab5: Lab5Like) extends FlatSpec {
  import lab5._

  "mapFirstDoWith" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     def dowith[W]: DoWith[W,List[Int]] = mapFirstWith(l1) { (i: Int) => if (i < 0) Some(doreturn(-i)) else None }
     assertResult((true,gold1)) { dowith(true) }
     assertResult((42,gold1)) { dowith(42) }
  }

  "mapWith(List)" should "map the elements of a list in a DoWith" in {
    val l = List(1, 2, 3, 4, 5)
    val r1 = l.map { i => i + 1 }

    def dowith1[W]: DoWith[W,List[Int]] = mapWith(l) { i: Int => doreturn(i + 1) }
    assertResult((true,r1)) { dowith1(true) }
    assertResult((42,r1)) { dowith1(42) }

    assertResult((2 * l.length + 1, r1)) {
      val dw: DoWith[Int,List[Int]] = mapWith(l) { i: Int =>
        domodify[Int](s => s + 2) map { _ => i + 1 }
      }
      dw(1)
    }
  }

  /*"mapWith(Map)" should "map the elements of a list in a DoWith" in {
    val m = Map("a" -> 1, "b" -> 2, "c" -> 3)
    val r1 = m.map { i => i + 1 }

    def dowith2[W]: DoWith[W,List[Int]] = mapWith(m) { i: Int => doreturn(m(i) + 1) }
    assertResult((true,r1)) { dowith2(true) }
    assertResult((42,r1)) { dowith2(42) }

    assertResult((2 * m.size + 1, r1)) {
      val dw: DoWith[Int,List[Int]] = mapWith(m) { i: Int =>
        domodify[Int](s => s + 2) map { _ => i + 1 }
      }
      dw(1)
    }
  }*/

  "rename" should "rename in a DoWith" in {
    val e1 = parse("const a = 1 + a; a")
    val e1p = parse("const aa = 1 + a; aa")

    assertResult((1,e1p)) {
      rename(empty, e1){ x => domodify[Int](n => n + 1) map { _ => x + x } }(0)
    }
  }

  "uniquify" should "uniquify with a counter for each variable" in {
    val e1 = parse("const a = 1; a")
    val e1p = parse("const a1 = 1; a1")
    val e2 = parse("const b = 2; b")
    val e2p = parse("const b0 = 2; b0")
    val e = Decl(MConst, "a", e1, e2)
    val ep = Decl(MConst, "a0", e1p, e2p)
    assertResult(ep) { uniquify(e) }
  }

  //Added testcases
  "myuniquify" should "uniquify variables as x with a global counter for each variable" in {
    val e1 = parse("const a = 1; a")
    val e1p = parse("const x1 = 1; x1")
    val e2 = parse("const b = 2; b")
    val e2p = parse("const x2 = 2; x2")
    val e = Decl(MConst, "a", e1, e2)
    val ep = Decl(MConst, "x0", e1p, e2p)
    assertResult(ep) { myuniquify(e) }
  }


  "isRedex" should "capture when expression e is reducible under a mode m" in {
    val t = true
    val f = false
    val e1 = parse("const a = 1; a")
    val e2 = parse("const b = 2; b")
    val ee = Decl(MConst, "a", e1, e2)
    val vale = N(1)
    var foo = 1
    foo = foo + 1
    val efoo = N(foo)
    assertResult(t) {isRedex(MConst, ee )}
    assertResult(f) {isRedex(MConst, vale)}
    val e11 = Var("y")
    assertResult(t) {isRedex(MVar,e11 )}
    assertResult(f) {isRedex(MVar, vale)}
    assertResult(t) {isRedex(MRef, e11)}
    val lval = !isLValue(efoo)
    assertResult(lval) {isRedex(MRef, efoo)}
  }



  /* Tests based on rules */

  "CastOkNull" should "perform CastOkNull" in {
    assertResult(true) {
      castOk(TNull, TObj(Map.empty))
    }
  }

  "DoNeg" should "return the negation of a number value" in {
    val e1 = N(5)
    val e2 = Unary(Neg, e1)
    assertResult( N(-5) ) {
      val (_, r) = step(e2)(memempty)
      r
    }
  }

  "DoNot" should "return opposite Boolean" in {
    val e1 = B(true)
    val e2 = Unary(Not, e1)
    assertResult( B(false) ) {
      val (_, r) = step(e2)(memempty)
      r
    }
  }

  "DoSeq" should "return result of sequential operations" in {
    val e1 = N(5)
    val e2 = N(100)
    val e3 = Binary(Seq, e1,e2)
    assertResult(e2) {
      val (_, r) = step(e3)(memempty)
      r
    }
  }

  "DoPlusString" should "return result of adding 2 strings" in {
    val e1 = S("hello")
    val e2 = S("there")
    val e3 = Binary(Plus, e1,e2)
    val e4 = S("hellothere")
    assertResult(e4) {
      val (_,r) = step(e3)(memempty)
      r
    }

  }

  "DoArith(plus)" should "return result of adding 2 number values" in {
    val e1 = N(1)
    val e2 = N(7)
    val e3 = Binary(Plus, e1,e2)
    val e4 = N(8)
    assertResult(e4) {
      val (_,r) = step(e3)(memempty)
      r
    }
  }

  "DoAndTrue" should "return true if both v1 and e2 are true" in {
    val v1 = B(true)
    val e2 = N(7)
    val e3 = Binary(And, v1, e2)
    val e4 = true
    assertResult(e2) {
      val (_,r) = step(e3)(memempty)
      r
    }
  }

  "DoAndFalse" should "return false if v1 is false without looking at e2" in {
    val v1 = B(false)
    val e2 = S("you weren't supposed to get here!")
    val e3 = Binary(And, v1, e2)
    assertResult(v1) {
      val (_,r) = step(e3)(memempty)
      r
    }
  }

  "DoOr" should "return true if either v1 or e2 is true" in {
    val v1 = B(false)
    val e2 = S("this is what is supposed to happen")
    val e3 = Binary(Or, v1, e2)
    assertResult(e2) {
      val (_,r) = step(e3)(memempty)
      r
    }
    val e5 = B(true)
    val e4 = Binary(Or, v1, e5)
    assertResult(e5) {
      val (_,r) = step(e4)(memempty)
      r
    }
  }

  "DoArith" should "perform arithmetic operations (Minus, Times, Div)" in {
    val v1 = N(100)
    val v2 = N(50)
    val v3 = N(50)
    val v4 = N(5000)
    val v5 = N(2)
    val e = Binary(Minus, v1, v2)
    val f = Binary(Times, v1,v2)
    val g = Binary(Div, v1,v2)
    assertResult(v3) {
      val (_,r) = step(e)(memempty)
      r
    }
    assertResult(v4) {
      val (_,r) = step(f)(memempty)
      r
    }
    assertResult(v5) {
      val (_,r) = step(g)(memempty)
      r
    }
  }

  "DoInequalityNumber" should "return result of calling inequality on 2 numbers" in {
    val v1 = N(100)
    val v2 = N(50)
    val v3 = N(50)
    val v4 = N(5000)
    val v5 = N(2)
    val e1 = Binary(Lt, v1,v2)
    val e2 = Binary(Le, v2,v3)
    val e3 = Binary(Gt, v4, v3)
    val e4 = Binary(Ge, v3,v1)
    val t = B(true)
    val f = B(false)
    assertResult(f) {
      val (_,r) = step(e1)(memempty)
      r
    }
    assertResult(t) {
      val (_,r) = step(e2)(memempty)
      r
    }
    assertResult(t) {
      val (_,r) = step(e3)(memempty)
      r
    }
    assertResult(f) {
      val (_,r) = step(e4)(memempty)
      r
    }
  }

  "DoInequalityString" should "return result of calling inequality on 2 strings" in {
    val v1 = S("hello")
    val v2 = S("hellothere")
    val v3 = S("hello")
    val v4 = S("teddy")
    val t = B(true)
    val f = B(false)
    val e1 = Binary(Lt, v1,v2)
    val e2 = Binary(Le, v2,v3)
    val e3 = Binary(Gt, v4, v3)
    val e4 = Binary(Ge, v3,v1)
    assertResult(t) {
      val (_,r) = step(e1)(memempty)
      r
    }
    assertResult(f) {
      val (_,r) = step(e2)(memempty)
      r
    }
    assertResult(t) {
      val (_,r) = step(e3)(memempty)
      r
    }
    assertResult(t) {
      val (_,r) = step(e4)(memempty)
      r
    }
  }

  "DoIfTrue" should "return e2 if v1 is true, else return e3" in {
    val v1 = B(true)
    val e2 = N(100)
    val e3 = N(200)
    val e4 = If(v1,e2,e3)
    assertResult(e2) {
      val (_,r) = step(e4)(memempty)
      r
    }
  }

  "DoIfFalse" should "return e3 if v1 is false" in {
    val v1 = B(false)
    val e2 = N(100)
    val e3 = N(200)
    val e4 = If(v1,e2,e3)
    assertResult(e3) {
      val (_,r) = step(e4)(memempty)
      r
    }

  }



  /* Search Rules Tests */

  "SearchDecl" should "step on non-reducible e1" in {
    val e1 = Decl(MConst, "x", Binary(Minus, N(100), N(75)), Undefined )
    val (wp, e1p) = step(e1)(memempty)
    assertResult(Decl(MConst,"x",N(25), Undefined)) {e1p}
  }






  // Probably want to write some tests for castOk, typeInfer, substitute, and step.

}

// An adapter class to pass in your Lab5 object.
class Lab5SpecRunner extends Lab5Spec(jsy.student.Lab5)

// The next bit of code runs a test for each .jsy file in src/test/resources/lab5.
// The test expects a corresponding .ans file with the expected result.
class Lab5JsyTests extends JavascriptyTester(None, "lab5", jsy.student.Lab5)

class Lab5Suite extends Suites(
  new Lab5SpecRunner,
  new Lab5JsyTests
)