package jsy.student

import jsy.lab5.Lab5Like

object Lab5 extends jsy.util.JsyApplication with Lab5Like {
  import jsy.lab5.ast._
  import jsy.util.DoWith
  import jsy.util.DoWith._

  /*
   * CSCI 3155: Lab 5
   * John Baker
   * Colin Bradley
   * Lauren Deans
   * Jose Gutierrez
   * Carter Reid
   *
   * Partner: <See Above>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*** Exercise with DoWith ***/

  /*** Rename bound variables in e ***/

  def rename[W](env: Map[String,String], e: Expr)(fresh: String => DoWith[W,String]): DoWith[W,Expr] = {
    def ren(env: Map[String,String], e: Expr): DoWith[W,Expr] = e match {
      case N(_) | B(_) | Undefined | S(_) => doreturn(e)
      case Print(e1) => ren(env,e1) map { e1p => Print(e1p) }

      case Unary(uop, e1) => ren(env,e1) map { e1p => Unary(uop, e1p) }
      case Binary(bop, e1, e2) => ren(env,e1) flatMap { e1p => ren(env,e2) map { e2p => Binary(bop, e1p, e2p) } }
      case If(e1, e2, e3) => ren(env,e1) flatMap { e1p => ren(env,e2) flatMap { e2p => ren(env,e3) map { e3p => If(e1p, e2p, e3p) } } }

      case Var(x) => if (env.contains(x)) doreturn(Var(lookup(env,x))) else doreturn(Var(x))  //Same as lab4, just need 'doreturn'

      case Decl(m, x, e1, e2) => fresh(x) flatMap { xp =>  //Create xp from x
        ren(env, e1) flatMap { e1p =>  //Create e1p from e1 (Use same as Lab4)
          ren(env + (x -> xp), e2) map { e2p =>  //Create e2p from e2 (Use same as Lab4)
            Decl(m, xp, e1p, e2p)  //Construct return Decl from computed parts above  (ie. Lab4 in pass-down steps)
          }
        }
      }

      case Function(p, params, tann, e1) => {
        val w: DoWith[W,(Option[String], Map[String,String])] = p match {
          case None => doreturn((None, env))
          case Some(x) => fresh(x) map { xp => (Some(xp), extend(env, x, xp))}
          //case Some(x) => doreturn((Some(fresh(x)), extend(env, x, fresh(x))))
          /*case Some(x) => fresh(x) flatMap { xp =>
            extend(env, x, fresh(x) map { envp =>
              (Some(xp), envp)
            }
          }*/
        }
        w flatMap { case (pp, envp) =>
          params.foldRight[DoWith[W,(List[(String,MTyp)],Map[String,String])]]( doreturn((Nil, envp)) ) {
            case ((x,mty), acc) => acc flatMap {
              ???
            }
          } flatMap {
            ???
          }
        }
      }

      case Call(e1, args) => ???

      case Obj(fields) => ???
      case GetField(e1, f) => ???

      case Null | A(_) => ???
      case Assign(e1, e2) => ???

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
    ren(env, e)
  }

  def myuniquify(e: Expr): Expr = {
    val fresh: String => DoWith[Int,String] = { _ =>  //Modify 'Uniqify' from Lab5Like.scala
      doget flatMap { i =>  //Get the existing/previous i (ie. get state)
        val xp = "x" + i  //Create string of x plus i
        doput(i + 1) map { _ => xp }  //Set updated i and  map to new variable name xp (ie. put state and map)
      }
    }
    val (_, r) = rename(empty, e)(fresh)(0)  //Run rename with empty environment and initialized/default to 0
    r  //return r (result)
  }

  /*** Helper: mapFirst to DoWith ***/

  // List map with an operator returning a DoWith
  def mapWith[W,A,B](l: List[A])(f: A => DoWith[W,B]): DoWith[W,List[B]] = {
    l.foldRight[DoWith[W,List[B]]]( doreturn(Nil) ) {  //Initialize foldRight to Nil/Empty DoWith List
      //Perform function on each item and keep accumulator as list
      (a, b) => b flatMap { bp => f(a) map { c => c :: bp } }
    }
  }

  // Map map with an operator returning a DoWith
  def mapWith[W,A,B,C,D](m: Map[A,B])(f: ((A,B)) => DoWith[W,(C,D)]): DoWith[W,Map[C,D]] = {
    m.foldRight[DoWith[W,Map[C,D]]]( doreturn(Map.empty) ) {  //Initialize foldRight to Nil/Empty DoWith Map
      //Perform function on each item and keep accumulator as mappings (add mapping to map)
      (a, b) => b flatMap { bp => f(a) map { c => bp + c } }
    }
  }

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](l: List[A])(f: A => Option[DoWith[W,A]]): DoWith[W,List[A]] = l match {
    //doreturn[W, R](r : R) creates a computation that leaves the state untouched,
    //but whose result is r
    case Nil => doreturn(l) //doget map { _ => l}
    case h :: t => f(h) match {
        //map method transforms a DoWith holding a computation with a W for a R to one for B using the callback f
      case None => mapFirstWith(t)(f) map  {(ft) => h :: ft}
      case Some(d) => d map {d => d :: t}
    }
  }

  // There are better ways to deal with the combination of data structures like List, Map, and
  // DoWith, but we won't tackle that in this assignment.

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
      /***** Make sure to replace the case _ => ???. */
    case (TNull, TObj(x)) => true  //Revise (Added for testcase passing, did not improve score)
    //Add more cases here
    //case_ ???
      /***** Cases for the extra credit. Do not attempt until the rest of the assignment is complete. */
    case (TInterface(tvar, t1p), _) => ???
    case (_, TInterface(tvar, t2p)) => ???
      /***** Otherwise, false. */
    case _ => false
  }

  /*** Type Inference ***/

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def isBindex(m: Mode, e: Expr): Boolean = m match {
    case MConst | MName | MVar => true
    case _ => false
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
        /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => val MTyp(m, t) = lookup(env, x); t
      // in the environment where x has typeof e1, e2 evaluates to type tau2
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }

      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (tgot1, tgot2) => err(tgot1, e1)
      }

      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (tgot1, tgot2) => err(tgot1, e1)
      }

      case Binary(Eq|Ne, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (typeE1, typeE2) if (!hasFunctionTyp(typeE1)) && (!hasFunctionTyp(typeE2)) => typeE1
        case (tgot1, tgot2) => err(tgot1, e1)
      }

      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TString
        case (TNumber, TNumber) => TNumber
        case (tgot1, tgot2) => err(tgot1, e1)
      }

      case Binary(And|Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (tgot1, tgot2) => err(tgot1, e1)
      }

      case Binary(Seq, e1, e2) => e2 match {
        case _ => typeof(env, e2)
      }

      case If(e1, e2, e3) => (typeof(env, e1), typeof(env, e2), typeof(env, e3)) match {
        case (TBool, typeE2, typeE3) => typeE2
        case (_, tgot2, tgot3) if tgot2 != tgot3 => err(tgot2, e2)
      }

      case Obj(fields) => TObj(fields mapValues( exp => typeof(env,exp)))
      case GetField(e1, f) => typeof(env, e1) match {
        case TObj(fields) => if (fields.contains(f)) fields(f) else throw StaticTypeError(typeof(env,e1),e1,e)
        case _ => throw StaticTypeError(typeof(env,e1),e1,e)
      }

        /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(m, x, e1, e2) => ???

      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = ???
        // Infer the type of the function body
        val t1 = ???
        // Check with the possibly annotated return type
        ???
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            ???
          }
          tret
        case tgot => err(tgot, e1)
      }

        /***** New cases for Lab 5. ***/
      case Assign(Var(x), e1) =>
        ???
      case Assign(GetField(e1, f), e2) =>
        ???
      case Assign(_, _) => err(TUndefined, e)

      case Null =>
        ???

      case Unary(Cast(t), e1) => typeof(env, e1) match {
        case tgot if ??? => ???
        case tgot => err(tgot, e1)
      }

      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3 and Lab 4.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) => (bop: @unchecked) match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (N(n1), N(n2)) => (bop: @unchecked) match {
        case Lt => n1 < n2
        case Le => n1 <= n2
        case Gt => n1 > n2
        case Ge => n1 >= n2
      }
    }
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_)  => e
      case Print(e1) => Print(subst(e1))

      /** *** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
      case Decl(mode, y, e1, e2) => if (y == x) Decl(mode, y, subst(e1), e2) else Decl(mode, y, subst(e1), subst(e2))

      /** *** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) =>
        if (params.exists((parameter: (String, MTyp)) => parameter._1 == x)) // if the parameter exists in the function, return the function
        //scala is 1 indexed like a bunch of savages
        // use ._1 to access the string in the parameter, use ._2 to access the MType
        //https://stackoverflow.com/questions/6884298/why-is-scalas-syntax-for-tuples-so-unusual
          Function(p, params, tann, e1)
        else
          Function(p, params, tann, subst(e1))
      // Need to do 2 checks: compare p (function name) to x and each parameter to x.
      // Also need to handle anonymous (no function name) case

      case Call(e1, args) => Call(subst(e1), args.map(arg => subst(arg))) //sub on function name and use map to sub args

      /** *** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.mapValues(e => subst(e)))
      case GetField(e1, f) => GetField(subst(e1), f)
        /***** New cases for Lab 5 */
        //added Null and A(_) cases above
      // case Null | A(_) => ???
      case Assign(e1, e2) => Assign(subst(e1), subst(e2))

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }

    def myrename(e: Expr): Expr = {
      val fvs = freeVars(esub) //from Lab4
      def fresh(x: String): String = if (fvs contains x) fresh(x + "$") else x //From Lab4

      rename[Unit](e)(doreturn(Nil)){ x => doreturn(fresh(x)) }
    }

    subst(myrename(e)) // change this line when you implement capture-avoidance #changed
  }

  /* Check whether or not an expression is reducible given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst | MVar if !isValue(e) => true //ValMode rule
    case MRef if !isLValue(e) => true //RefMode rule
    case _ => false
    }



  def getBinding(mode: Mode, e: Expr): DoWith[Mem,Expr] = {
    require(!isRedex(mode,e), s"expression ${e} must not reducible under mode ${mode}")
    mode match {
      case MConst => doreturn(e) //ConstBind rule
      case MName => doreturn(e) //NameBind rule
      case MRef => doreturn(e) //RefBind rule
      case MVar => memalloc(e) map { a => Unary(Deref, a) } //memalloc from ast.scala

    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
        /***** Cases needing adapting from Lab 3. */
        //DoNeg
      case Unary(Neg, v1) if isValue(v1) => v1 match {
        case N(n1) => doreturn(N(-n1))
        case _ => throw StuckError(e)}
        //DoNot
      case Unary(Not, v1) if isValue(v1) => v1 match {
        case B(b1) => doreturn(B(!b1))
        case _ => throw StuckError(e)}
        //DoSeq
      case Binary(Seq, v1, e2) if isValue(v1) => doreturn(e2)
        //DoPlusString & DoArith(+)
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) =>
        (v1, v2) match {
          case (S(s1), S(s2)) => doreturn(S(s1 + s2))
          case (N(n1), N(n2)) => doreturn(N(n1 + n2))
          case _ => throw StuckError(e)

      }
        //DoEquality
      case Binary( bop @ (Eq|Ne), v1, v2) if isValue(v1) && isValue(v2) =>
        bop match {
          case Eq => doreturn(B(v1 == v2))
          case Ne => doreturn(B(v1 != v2))
        }





        /***** More cases here */
        /***** Cases needing adapting from Lab 4. */
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) =>
        ???
      case GetField(a @ A(_), f) =>
        ???

      case Decl(MConst, x, v1, e2) if isValue(v1) =>
        ???
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        ???

        /***** New cases for Lab 5. */
      case Unary(Deref, a @ A(_)) =>
        ???

      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] { m => ??? } map { _ => ??? }

      case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
        ???

      case Call(v @ Function(p, params, _, e), args) => {
        val pazip = params zip args
        if (???) {
          val dwep = pazip.foldRight( ??? : DoWith[Mem,Expr] )  {
            case (((xi, MTyp(mi, _)), ei), dwacc) => ???
          }
          p match {
            case None => ???
            case Some(x) => ???
          }
        }
        else {
          val dwpazipp = mapFirstWith(pazip) {
            ???
          }
          ???
        }
      }

      /* Base Cases: Error Rules */
        /***** Replace the following case with a case to throw NullDeferenceError.  */
      //case _ => throw NullDeferenceError(e)

      /* Inductive Cases: Search Rules */
      case Print(e1) => step(e1) map { e1p => Print(e1p) }
        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(uop, e1) => ???
        /***** Cases needing adapting from Lab 4 */
      case GetField(e1, f) =>
        ???
      case Obj(fields) =>
        ???

      case Decl(mode, x, e1, e2) =>
        ???
      case Call(e1, args) =>
        ???

        /***** New cases for Lab 5.  */
      case Assign(e1, e2) if ??? =>
        ???
      case Assign(e1, e2) =>
        ???

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** Extra Credit: Lowering: Remove Interface Declarations ***/

  def lower(e: Expr): Expr =
    /* Do nothing by default. Change to attempt extra credit. */
    e

  /*** External Interfaces ***/

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}
