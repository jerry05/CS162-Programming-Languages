package cs162.lapel

//——————————————————————————————————————————————————————————————————————————————
// Abstract syntax

// x ∈ Variable  f ∈ FunctionSymbol  p ∈ PredicateSymbol
//    t ∈ Term    ::= x | f(t⋯)
//    g ∈ Goal    ::= p(t⋯) | g1 ∧ g2 | g1 ∨ g2 | a ⊃ g | ∃x⋯.g | output
//    a ∈ Assume  ::= p(t⋯) | p(t⋯) ⊂ g | ∀x⋯.a
// prog ∈ Program ::= a⋯ ⊢ g

sealed abstract class Term

case class Var(name: String) extends Term

case class Function(name: String, args: Seq[Term]) extends Term

sealed abstract class Goal

case class Predicate(name: String, args: Seq[Term]) extends Goal

case class Conjunct(g1: Goal, g2: Goal) extends Goal

case class Disjunct(g1: Goal, g2: Goal) extends Goal

case class Hypothetical(a: Assume, g: Goal) extends Goal

case class Exists(vars: Set[Var], g: Goal) extends Goal

case class Output() extends Goal

// we'll assume that all assumptions are universally quantified, and
// the ones that aren't will just have the empty set of variables
sealed abstract class Assume

case class Fact(vars: Set[Var], pred: Predicate) extends Assume

case class Clause(vars: Set[Var], hd: Predicate, body: Goal) extends Assume

case class Program(as: Seq[Assume], query: Goal)


//——————————————————————————————————————————————————————————————————————————————
// Values and equivalence classes

// values are ground terms (functions without any variables) where
// "ground" includes logic variables standing for unknown terms
//
// the 'contains' method returns whether or not a value contains a
// given logic variable; it's used for the unification occurs check
//
sealed abstract class Value {
  def contains(x: LogicV): Boolean
}

case class FunV(name: String, args: Seq[Value]) extends Value {
  def contains(x: LogicV) = args exists (_ contains x)
}

case class LogicV(id: Int) extends Value {
  def contains(x: LogicV) = x == this
}

// create unique logic variables using "LogicV()"; this should be the
// only way that logic variables are ever created during execution in
// order to ensure freshness
object LogicV {
  private var counter = 0

  def apply(): LogicV = {
    counter += 1;
    LogicV(counter)
  }
}

// equivalence classes involving logic variables (functions are always
// the set representative if they are present in an equivalence class)
case class Equiv(eq: Map[LogicV, Value]) {
  // look up a value and return its set representative in the
  // equivalence class
  def apply(v: Value): Value = v match {
    case logicV: LogicV => if (eq.get(logicV).isDefined) apply(eq(logicV)) else logicV
    case FunV(name, args) => FunV(name, args.map(apply))
    case _ => v
  }

  // unify two values
  def unify(v1: Value, v2: Value): Option[Equiv] = (apply(v1), apply(v2)) match {
    case (funV_1@FunV(name_1, args_1), funV_2@FunV(name_2, args_2)) =>
      if (name_1 != name_2 || args_1.length != args_2.length) None
      else args_1.zip(args_2).foldLeft(Some(Equiv(eq)): Option[Equiv])((option, tuple) => option match {
        case Some(equiv) => equiv.unify(tuple._1, tuple._2)
        case _ => None
      })
    case (logicV_1@LogicV(id_1), logicV_2@LogicV(id_2)) => if (logicV_1 == logicV_2 || id_1 == id_2) Some(Equiv(eq)) else Some(Equiv(eq + (logicV_1 -> logicV_2)))
    case (logicV@LogicV(id), funV@FunV(name, arg)) => if (funV.contains(logicV)) None else Some(Equiv(eq + (logicV -> funV)))
    case (funV@FunV(name, arg), logicV@LogicV(id)) => if (funV.contains(logicV)) None else Some(Equiv(eq + (logicV -> funV)))
    case _ => None
  }

  // translate a value into a string, mapping logic variables to
  // functions wherever possible
  def valToString(v: Value): String =
    apply(v) match {
      case LogicV(id) ⇒ "L" + id
      case FunV(name, args) ⇒
        if (args.size == 0) name
        else name + "(" + (args map valToString).mkString(", ") + ")"
    }
}


//——————————————————————————————————————————————————————————————————————————————
// Interpreter

import scala.io.Source.fromFile
import scala.language.postfixOps

// the main entry point of the interpreter
object Interpreter {
  // environments map variables to logic variables
  type Env = Map[Var, LogicV]

  // closures contain a goal, its environment, and the assumptions
  // that can be used to prove the goal
  case class Closure(g: Goal, env: Env, as: Seq[Assume])

  // entry point
  def main(args: Array[String]) {
    if (args.length < 1) sys.error("need to provide a filename")
    val filename = args(0)
    val input = fromFile(filename).mkString

    val prog = LPLParser.program.run(input, filename) match {
      case Left(error) ⇒ sys.error("parse error: " + error)
      case Right(p) ⇒ p
    }

    eval(
      Seq(Closure(prog.query, Map(), prog.as)),
      Equiv(Map())
    )
  }

  // finds all satisfying solutions to the given stack of closures
  // using the given equivalence relation (where the stack is
  // represented by a sequence, with the head of the sequence being
  // the top of the stack)
  def eval(goals: Seq[Closure], eq: Equiv): Unit =
    if (goals nonEmpty) goals.head match {
      // atomic predicate goal
      case goalClo@Closure(p: Predicate, env, as) ⇒ as.map(_ match {
        case Fact(vars, pred) => matchPredicates(Closure(pred, vars.map(_ -> LogicV()).toMap, as), goalClo, eq) match {
          case Some(equiv) => eval(goals.tail, equiv)
          case _ => Unit
        }
        case Clause(vars, hd, body) =>
          val varToLogicV = vars.map(_ -> LogicV()).toMap
          matchPredicates(Closure(hd, varToLogicV, as), goalClo, eq) match {
            case Some(equiv) => eval(Closure(body, varToLogicV, as) +: goals.tail, equiv)
            case _ => Unit
          }
        case _ => Unit
      })

      // conjunct goal
      case Closure(Conjunct(g1, g2), env, as) ⇒
        val c1 = Closure(g1, env, as)
        val c2 = Closure(g2, env, as)
        eval(c1 +: c2 +: goals.tail, eq)

      // disjunct goal
      case Closure(Disjunct(g1, g2), env, as) ⇒
        val c1 = Closure(g1, env, as)
        val c2 = Closure(g2, env, as)
        val tail = goals.tail
        eval(c1 +: tail, eq)
        eval(c2 +: tail, eq)

      // hypothetical implication goal
      case Closure(Hypothetical(a, g), env, as) ⇒
        eval(Closure(g, env, a +: as) +: goals.tail, eq)

      // existential quantification goal
      case Closure(Exists(vars, g), env, as) ⇒
        eval(Closure(g, vars.foldLeft(env)((tmp, value) => tmp + (value -> LogicV())), as) +: goals.tail, eq)

      // output goal
      case Closure(_: Output, env, _) ⇒
        if (env nonEmpty) {
          env map {
            case (x, v) ⇒ println(x.name + " ↦ " + eq.valToString(v))
          }
        }
        else println("true")
        println("========")
        eval(goals.tail, eq)
    }

  // HELPER FUNCTION USED BY THE "ATOMIC PREDICATE GOAL" CASE ABOVE
  //
  // given an "assumption closure" for a predicate coming from a fact
  // or the head of a clause (aClo) and a "goal closure" for the
  // current goal (gClo) and the current equivalence relation (eq),
  // try to match up the assumption and the goal, potentially creating
  // a new equivalence relation in the process
  //
  // this will be the method by which we determine whether a given
  // assumption can help us prove a given atomic predicate goal
  def matchPredicates(aClo: Closure, gClo: Closure, eq: Equiv): Option[Equiv] = (aClo.g, gClo.g) match {
    case (Predicate(name_1, args_1), Predicate(name_2, args_2)) =>
      if (name_1 != name_2 || args_1.size != args_2.size) None
      else {
        val map_1: Seq[Value] = args_1.map(termToValue(_, aClo.env))
        val map_2: Seq[Value] = args_2.map(termToValue(_, gClo.env))
        val zippedTuples: Seq[(Value, Value)] = map_1.zip(map_2)
        zippedTuples.foldLeft[Option[Equiv]](Some(eq))((option, tuple) => option match {
            case Some(equiv) => equiv.unify(tuple._1, tuple._2)
            case _ => None
          })
      }
    case _ => None
  } // FILL ME IN

  // HELPER FUNCTION USED BY "matchPredicates"
  //
  // transform a term (i.e., variable or function on terms) into a
  // value (i.e., logic variable or function on values)
  def termToValue(t: Term, env: Env): Value =
    t match {
      case x: Var ⇒ env(x)
      case Function(name, args) ⇒ FunV(name, args map (termToValue(_, env)))
    }
}


//——————————————————————————————————————————————————————————————————————————————
// Parser
//
// — see the test programs test〈X〉.lpl for examples of concrete syntax.

import scala.language.implicitConversions
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.syntactical.StdTokenParsers

object LPLParser extends StdTokenParsers with PackratParsers {
  type Parser[T] = PackratParser[T]
  type Error = String
  type Tokens = StdLexical

  val lexical = new StdLexical

  lexical.delimiters ++= Seq(".", "(", ")", ":-", ",", ";", "{", "}", "?", "=>")
  lexical.reserved ++= Seq("output")

  class Runnable[A](val xs: Parser[A]) {
    def run(stream: String, filename: String): Either[Error, A] = {
      val commentFree = stream.replaceAll("--.*", "")
      val tokens = new lexical.Scanner(commentFree)

      phrase(xs)(tokens) match {
        case e: NoSuccess ⇒ Left(e.toString)
        case Success(res, _) ⇒ {
          /*println(res);*/ Right(res)
        }
      }
    }
  }

  implicit def parserToRunnable[A](p: Parser[A]): Runnable[A] = new Runnable(p)

  lazy val program: Parser[Program] =
    (factOrClause *) ~ "?" ~ goal ~ "." ^^ {
      case fcs ~ "?" ~ g ~ "." ⇒ Program(fcs, g)
    }

  lazy val factOrClause: Parser[Assume] =
    fact | clause

  lazy val fact: Parser[Fact] =
    (vars ~ predicate ~ "." ^^ { case v ~ p ~ "." ⇒ Fact(v, p) } |
      predicate ~ "." ^^ { case p ~ "." ⇒ Fact(Set(), p) }
      )

  lazy val clause: Parser[Clause] =
    (vars ~ predicate ~ ":-" ~ goal ~ "." ^^ {
      case v ~ p ~ ":-" ~ g ~ "." ⇒ Clause(v, p, g)
    } |
      predicate ~ ":-" ~ goal ~ "." ^^ {
        case p ~ ":-" ~ g ~ "." ⇒ Clause(Set(), p, g)
      }
      )

  lazy val factOrClauseNoDot: Parser[Assume] =
    clauseNoDot | factNoDot | "(" ~> factOrClauseNoDot <~ ")"

  lazy val factNoDot: Parser[Fact] =
    (vars ~ predicate ^^ { case v ~ p ⇒ Fact(v, p) } |
      predicate ^^ { case p ⇒ Fact(Set(), p) })

  lazy val clauseNoDot: Parser[Clause] =
    (vars ~ predicate ~ ":-" ~ goal ^^ {
      case v ~ p ~ ":-" ~ g ⇒ Clause(v, p, g)
    } |
      predicate ~ ":-" ~ goal ^^ {
        case p ~ ":-" ~ g ⇒ Clause(Set(), p, g)
      }
      )

  lazy val vars: Parser[Set[Var]] =
    "{" ~> repsep(upperid, ",") <~ "}" ^^ {
      case vs ⇒ vs.map(v ⇒ Var(v)).toSet
    }

  lazy val goal: Parser[Goal] =
    conjunct | disjunct | hypothetical | output | predicate | exists | parens

  lazy val parens: Parser[Goal] =
    "(" ~> goal <~ ")"

  lazy val predicate: Parser[Predicate] =
    ident2 ~ "(" ~ repsep(term, ",") ~ ")" ^^ {
      case id ~ "(" ~ tms ~ ")" ⇒ Predicate(id, tms)
    }

  lazy val conjunct: Parser[Conjunct] =
    goal ~ "," ~ goal ^^ { case g1 ~ "," ~ g2 ⇒ Conjunct(g1, g2) }

  lazy val disjunct: Parser[Disjunct] =
    goal ~ ";" ~ goal ^^ { case g1 ~ ";" ~ g2 ⇒ Disjunct(g1, g2) }

  lazy val hypothetical: Parser[Hypothetical] =
    factOrClauseNoDot ~ "=>" ~ goal ^^ { case a ~ _ ~ g ⇒ Hypothetical(a, g) }

  lazy val exists: Parser[Exists] =
    vars ~ goal ^^ { case vs ~ g ⇒ Exists(vs, g) }

  lazy val output: Parser[Output] =
    "output" ^^^ Output()

  lazy val term: Parser[Term] =
    function | ident2 ^^ {
      case s ⇒
        if (Character.isUpperCase(s.charAt(0))) Var(s) else Function(s, Seq())
    }

  lazy val function: Parser[Function] =
    ident2 ~ "(" ~ repsep(term, ",") ~ ")" ^^ {
      case id ~ "(" ~ tms ~ ")" ⇒ Function(id, tms)
    }

  lazy val ident2: Parser[String] =
    numericLit ~ ident ^^ { case n ~ i ⇒ n + i } | ident | numericLit

  lazy val upperid: Parser[String] =
    ident flatMap { s ⇒ {
      if (Character.isUpperCase(s.charAt(0)))
        success(s)
      else
        failure("unexpected lowercase letter")
    }
    }
}
