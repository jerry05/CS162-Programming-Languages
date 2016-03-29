import cs162.assign4.syntax.Aliases._
import cs162.assign4.syntax._

import scala.io.Source.fromFile

//——————————————————————————————————————————————————————————————————————————————
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
          println(Pretty.prettySyntax(program))
          getType(program.e, new TypeEnv())
          println("This program is well-typed")
        } catch {
          case Illtyped => println("This program is ill-typed")
        }
    }
  }

  // Gets a listing of the constructor names associated with a given type definition.
  // For example, consider the following type definition:
  //
  // type Either['A, 'B] = Left 'A | Right 'B
  //
  // Some example calls to `constructors`, along with return values:
  //
  // constructors("Either") = Set("Left", "Right")
  // constructors("Foo") = a thrown Illtyped exception
  //
  def constructors(name: Label): Set[Label] =
    typeDefs.find(_.name == name).map(_.constructors.keySet).getOrElse(throw Illtyped)

  // Takes the following parameters:
  // -The name of a user-defined type
  // -The name of a user-defined constructor in that user-defined type
  // -The types which we wish to apply to the constructor
  // Returns the type that is held within the constructor.
  //
  // For example, consider the following type definition:
  //
  // type Either['A, 'B] = Left 'A | Right 'B
  //
  // Some example calls to `constructorType`, along with return values:
  //
  // constructorType("Either", "Left", Seq(NumT, BoolT)) = NumT
  // constructorType("Either", "Right", Seq(NumT, BoolT)) = BoolT
  // constructorType("Either", "Left", Seq(NumT)) = a thrown Illtyped exception
  // constructorType("Either", "Right", Seq(BoolT)) = a thrown Illtyped exception
  // constructorType("Either", "Foo", Seq(UnitT)) = a thrown Illtyped exception
  // constructorType("Bar", "Left", Seq(UnitT)) = a thrown Illtyped exception
  //
  def constructorType(name: Label, constructor: Label, types: Seq[Type]): Type =
    (for {
      td <- typeDefs
      rawType <- td.constructors.get(constructor)
      if (types.size == td.tvars.size)
    } yield replace(rawType, td.tvars.zip(types).toMap)).headOption.getOrElse(throw Illtyped)

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

  // Given a type and a mapping of type variables to other types, it
  // will recursively replace the type variables in `t` with the
  // types in `tv2t`, if possible.  If a type variable isn't
  // in `tv2t`, it should simply return the original type.  If a
  // `TFunT` is encountered, then whatever type variables it defines
  // (the first parameter in the `TFunT`) should overwrite whatever is in
  // `tv2t` right before a recursive `replace` call.  In other words,
  // type variables can shadow other type variables.
  //
  def replace(t: Type, tv2t: Map[TVar, Type]): Type =
    t match {
      case NumT | BoolT | UnitT => t

      case FunT(params, ret) => FunT(params.map((typo: Type) => replace(typo, tv2t)), replace(ret, tv2t))

      case RcdT(fields) => RcdT(fields.mapValues(replace(_, tv2t)))

      case TypT(name, typs) => TypT(name, typs.map((typo: Type) => replace(typo, tv2t)))

      case tv: TVar => tv2t.getOrElse(tv, t)

      case TFunT(tvars, funt) => TFunT(tvars, replace(funt, tv2t -- tvars).asInstanceOf[FunT])
    }

  // HINT - the bulk of this remains unchanged from the previous assignment.
  // Feel free to copy and paste code from your last submission into here.
  def getType(e: Exp, env: TypeEnv): Type =
    e match {
      case x: Var => env.getOrElse(x, throw Illtyped)

      case _: Num => NumT

      case _: Bool => BoolT

      case _: Unit => UnitT

      case Plus | Minus | Times | Divide => FunT(Seq(NumT, NumT), NumT)

      case LT | EQ => FunT(Seq(NumT, NumT), BoolT)

      case And | Or => FunT(Seq(BoolT, BoolT), BoolT)

      case Not => FunT(Seq(BoolT), BoolT)

      case Fun(params, body) =>
        val newEnv = params.foldLeft(env)((accum, envtype) => accum + (envtype._1 -> envtype._2))
        val newType = getType(body, newEnv)
        val newSeq = params.foldLeft(Seq[Type]())((accum, envtype) => accum :+ envtype._2)
        FunT(newSeq, newType)

      case Call(fun, args) => getType(fun, env) match {
        case FunT(params, result) =>
          // Bail if no match
          if (args.map(args => getType(args, env)) != params) throw Illtyped

          // Return result
          result
        case _ => throw Illtyped
      }

      case If(e1, e2, e3) => getType(e1, env) match {
        case BoolT =>
          // Bail if no match
          val result = getType(e2, env)
          if (result != getType(e3, env)) throw Illtyped

          // Return result
          result
        case _ => throw Illtyped
      }

      case Let(x, e1, e2) => getType(e2, env + (x -> getType(e1, env)))

      case Rec(x, t1, e1, e2) =>
        // Bail if no match
        if (getType(e1, env + (x -> t1)) != t1) throw Illtyped

        // Return result
        getType(e2, env + (x -> t1))

      case Record(fields) => RcdT(fields.map(t => t._1 -> getType(t._2, env)))

      case Access(e, field) =>
        getType(e, env) match {
          case RcdT(fields) => fields.getOrElse(field, throw Illtyped)
          case _ => throw Illtyped
        }

      case c@Construct(constructor, typs, e) =>
        val name = typename(constructor)
        if (constructorType(name, constructor, typs) == getType(e, env)) TypT(name, typs)
        else throw Illtyped

      case Match(e, cases) => getType(e, env) match {
        case TypT(name, typ) =>
          // Get all of the types for the constructor values and put them in a list
          val typeConstructorValuesList = cases.map(tuple => getType(tuple._3, env + (tuple._2 -> constructorType(name, tuple._1, typ))))

          // Bail if:
          // (1) Ordered label list doesn't match the ordered constructor label list or
          // (2) there are multiple (different) types in the constructor list
          if (cases.map(tuple => tuple._1).sorted != constructors(name).toSeq.sorted ||
            typeConstructorValuesList.distinct.length != 1) throw Illtyped

          // Since there is only type in the collapsed constructor list, return the first (only) element type
          typeConstructorValuesList.head
        case _ => throw Illtyped
      }

      case TAbs(tvars, fun) => getType(fun, env) match {
        case funt: FunT => TFunT(tvars, funt)
        case _ => throw Illtyped
      }

      case TApp(e, typs) => getType(e, env) match {
        case TFunT(tvars, funt) => replace(funt, tvars.zip(typs).toMap)
        case _ => throw Illtyped
      }
    }
}
