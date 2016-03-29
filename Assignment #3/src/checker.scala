import cs162.assign3.syntax.Aliases._
import cs162.assign3.syntax._

import scala.io.Source.fromFile

//—————————————————————————————————————————————————————————————————————————
// Main entry point

object Checker {
  type TypeEnv = scala.collection.immutable.HashMap[Var, Type]

  object Illtyped extends Exception

  var typeDefs = Set[TypeDef]()

  def main(args: Array[String]) {
    val filename = args(0)
    val input = fromFile(filename).mkString
    Parsers.program.run(input, filename) match {
      case Left(e) => println(e)
      case Right(program) =>
        val prettied = Pretty.prettySyntax(program)
        typeDefs = program.typedefs

        try {
          getType(program.e, new TypeEnv())
          println("This program is well-typed:\n")
          println(Pretty.prettySyntax(program))
        } catch {
          case Illtyped => println("This program is ill-typed")
        }
    }
  }

  // Gets all the constructors associated with a given type name.
  // For example, consider the following typedefs:
  //
  // type Either = Left num | Right bool
  // type Maybe = Some num | None
  //
  // With respect to the above typedefs, `constructors` will return
  // the following underneath the given arguments:
  //
  // constructors(Label("Either")) = Map(Label("Left") -> NumT, Label("Right") -> BoolT)
  // constructors(Label("Maybe")) = Map(Label("Some") -> NumT, Label("None") -> UnitT)
  // constructors(Label("Fake")) throws Illtyped
  //
  def constructors(name: Label): Map[Label, Type] =
    typeDefs.find(_.name == name).map(_.constructors).getOrElse(throw Illtyped)

  // Gets the type of the constructor.
  // For example, considering the typedefs given in the `constructors` comment above,
  // `typename` will return the following with the given arguments:
  //
  // typename(Label("Left")) = Label("Either")
  // typename(Label("Right")) = Label("Either")
  // typename(Label("Some")) = Label("Maybe")
  // typename(Label("None")) = Label("Maybe")
  //
  def typename(constructor: Label): Label =
    typeDefs.find(_.constructors.contains(constructor)).getOrElse(throw Illtyped).name

  def getType(e: Exp, env: TypeEnv): Type =
    e match {
      // variables
      case x: Var => env.getOrElse(x, throw Illtyped)

      // numeric literals
      case _: Num => NumT

      // boolean literals
      case _: Bool => BoolT

      // `nil` - the literal for unit
      case _: NilExp => UnitT

      // builtin arithmetic operators
      case Plus | Minus | Times | Divide => FunT(Seq(NumT, NumT), NumT)

      // builtin relational operators
      case LT | EQ => FunT(Seq(NumT, NumT), BoolT)

      // builtin logical operators
      case And | Or => FunT(Seq(BoolT, BoolT), BoolT)

      // builtin logical operators
      case Not => FunT(Seq(BoolT), BoolT)

      // function creation
      case Fun(params, body) =>
        val newEnv = params.foldLeft(env)((accum, envtype) => accum + (envtype._1 -> envtype._2))
        val newType = getType(body, newEnv)
        val newSeq = params.foldLeft(Seq[Type]())((accum, envtype) => accum :+ envtype._2)
        FunT(newSeq, newType)

      // function call
      case Call(fun, args) =>
        getType(fun, env) match {
          case FunT(params, result) =>
            // Bail if no match
            if (args.map(args => getType(args, env)) != params) throw Illtyped

            // Return result
            result
          case _ => throw Illtyped
        }

      // conditionals 
      case If(e1, e2, e3) =>
        getType(e1, env) match {
          case BoolT =>
            // Bail if no match
            val result = getType(e2, env)
            if (result != getType(e3, env)) throw Illtyped

            // Return result
            result
          case _ => throw Illtyped
        }

      // let binding
      case Let(x, e1, e2) => getType(e2, env + (x -> getType(e1, env)))

      // recursive binding
      case Rec(x, t1, e1, e2) =>
        // Bail if no match
        if (getType(e1, env + (x -> t1)) != t1) throw Illtyped

        // Return result
        getType(e2, env + (x -> t1))

      // record literals
      case Record(fields) => RcdT(fields.map(t => t._1 -> getType(t._2, env)))

      // record access
      case Access(e, field) =>
        getType(e, env) match {
          case RcdT(fields) => fields.getOrElse(field, throw Illtyped)
          case _ => throw Illtyped
        }

      // constructor use
      case Construct(constructor, e) =>
        val name = typename(constructor)
        if (constructors(name).getOrElse(constructor, throw Illtyped) != getType(e, env)) throw Illtyped

        TypT(name)

      // pattern matching (case ... of ...)
      case Match(e, cases) =>
        getType(e, env) match {
          case TypT(name) =>
            // Get all of the types for the constructor values and put them in a list
            val typeConstructorValuesList = cases.map(tuple => getType(tuple._3, env + (tuple._2 -> constructors(name).getOrElse(tuple._1, throw Illtyped))))

            // Bail if:
            // (1) Ordered label list doesn't match the ordered constructor label list or
            // (2) there are multiple (different) types in the constructor list
            if (cases.map(tuple => tuple._1).sorted != constructors(name).keys.toSeq.sorted ||
              typeConstructorValuesList.distinct.length != 1) throw Illtyped

            // Since there is only type in the collapsed constructor list, return the first (only) element type
            typeConstructorValuesList.head
          case _ => throw Illtyped
        }
    }
}
