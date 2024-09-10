package br.unb.cic.oberon.tc

import br.unb.cic.oberon.tc.StateOrErrorMonad._

import br.unb.cic.oberon.ir.ast._
import br.unb.cic.oberon.environment.Environment
import br.unb.cic.oberon.visitor.OberonVisitorAdapter

import cats.data.State
import cats.data.StateT
import org.antlr.stringtemplate.language.FormalArgument

object TypeChecker {
  val comparableTypes = List(IntegerType, RealType)
  val numericTypes = List(IntegerType, RealType)

  def checkExpression(exp: Expression): StateOrError[Type] = {
    exp match {
      case IntValue(_)         => pure(IntegerType)
      case RealValue(_)        => pure(RealType)
      case CharValue(_)        => pure(CharacterType)
      case BoolValue(_)        => pure(BooleanType)
      case StringValue(_)      => pure(StringType)
      case Location(_)         => pure(LocationType)
      case NullValue           => pure(NullType)
      case Undef()             => assertError("Undefined type.")
      case VarExpression(name) => lookupVariable(name)
      case EQExpression(l, r) =>
        checkOperation(l, r, comparableTypes, BooleanType)
      case NEQExpression(l, r) =>
        checkOperation(l, r, comparableTypes, BooleanType)
      case GTExpression(l, r) =>
        checkOperation(l, r, comparableTypes, BooleanType)
      case LTExpression(l, r) =>
        checkOperation(l, r, comparableTypes, BooleanType)
      case GTEExpression(l, r) =>
        checkOperation(l, r, comparableTypes, BooleanType)
      case LTEExpression(l, r) =>
        checkOperation(l, r, comparableTypes, BooleanType)
      case AddExpression(l, r)  => checkOperationKeepType(l, r, numericTypes)
      case SubExpression(l, r)  => checkOperationKeepType(l, r, numericTypes)
      case MultExpression(l, r) => checkOperationKeepType(l, r, numericTypes)
      case DivExpression(l, r)  => checkOperationKeepType(l, r, numericTypes)
      case ModExpression(l, r)  => checkOperationKeepType(l, r, numericTypes)
      case AndExpression(l, r) =>
        checkOperation(l, r, List(BooleanType), BooleanType)
      case OrExpression(l, r) =>
        checkOperation(l, r, List(BooleanType), BooleanType)
      case NotExpression(exp) =>
        for {
          t <- checkExpression(exp)
          r <- enforceType(t, BooleanType)
        } yield r
      case Brackets(exp) => checkExpression(exp)
      case FunctionCallExpression(name: String, args: List[Expression]) => {
        for {
          p <- lookupProcedure(name)
          ts <- checkExpressions(args)
          _ <-
            if (p.args.map[Type](fa => fa.argumentType) == ts) { pure(()) }
            else {
              assertError(s"Wrong type for argument of function ${name}.")
            }
          r <- p.returnType match {
            case None    => pure(UndefinedType)
            case Some(r) => pure(r)
          }
        } yield r
      }
      case ArrayValue(values, arrayType) =>
        for {
          ts <- checkExpressions(values.toList)
          _ <- enforceTypes(ts, arrayType.baseType)
        } yield arrayType
      case ArraySubscript(array: Expression, index: Expression) => {
        for {
          at <- checkExpression(array)
          it <- checkExpression(index)
          r <- at match {
            case ArrayType(_, bt) =>
              it match {
                case IntegerType => pure(bt)
                case _ =>
                  assertError(
                    s"Tried to subscript array with index of type ${it}. Expected IntegerType!"
                  )
              }
            case _ =>
              assertError(
                s"Tried to subscript element of type ${at}. Expected ArrayType!"
              )
          }
        } yield r
      }
      case FieldAccessExpression(exp: Expression, attributeName: String) => {
        for {
          t <- checkExpression(exp)
          r <- t match {
            case RecordType(vars) =>
              vars.find(v => v.name == attributeName) match {
                case Some(v) => pure(v.variableType)
                case None =>
                  assertError(
                    s"Tried to access record with field ${attributeName} which does not exist."
                  )
              }
            case ReferenceToUserDefinedType(name) =>
              StateT[ErrorOr, Environment[Type], Type](
                (env: Environment[Type]) => {
                  env.lookupUserDefinedType(name) match {
                    case Some(UserDefinedType(_, RecordType(vars))) => {
                      vars.find(v => v.name == attributeName) match {
                        case Some(v) => Right((env, v.variableType))
                        case None =>
                          Left(
                            s"Tried to access field from ${name} with field ${attributeName} which does not exist."
                          )
                      }
                    }
                    case _ =>
                      Left(
                        s"Tried to access field from user-defined type ${name} but type does not exist."
                      )
                  }
                }
              )
            case _ =>
              assertError(
                s"Tried to access field from type ${t}. Expected RecordType."
              )
          }
        } yield r
      }
      case PointerAccessExpression(name: String) =>
        StateT[ErrorOr, Environment[Type], Type]((env: Environment[Type]) => {
          env.lookup(name) match {
            case Some(PointerType(vt)) => Right((env, vt))
            case _ => Left(s"Could not find pointer with name ${name}.")
          }
        })
      case LambdaExpression(args: List[FormalArg], exp: Expression) =>
        StateT[ErrorOr, Environment[Type], Type]((env: Environment[Type]) => {
          // We insert those argument into our environment and then evaluate the
          // expression
          val nEnv = args.foldRight[Environment[Type]](env)(
            (arg: FormalArg, acc: Environment[Type]) =>
              acc.setLocalVariable(arg.name, arg.argumentType)
          )

          checkExpression(exp).runA(nEnv) match {
            case Left(err) => Left(err)
            case Right(t)  => Right((env, t))
          }
        })
    }
  }

  def checkModule(module: OberonModule): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  def checkStmt(stmt: Statement): StateOrError[Type] = stmt match {
    case ReadLongRealStmt(v: String) => {
      for {
        t <- lookupVariable(v)
        r <- enforceType(t, RealType)
      } yield r
    }
    case ReadRealStmt(v: String) => {
      for {
        t <- lookupVariable(v)
        r <- enforceType(t, RealType)
      } yield r
    }
    case ReadLongIntStmt(v: String) => {
      for {
        t <- lookupVariable(v)
        r <- enforceType(t, IntegerType)
      } yield r
    }
    case ReadIntStmt(v: String) => {
      for {
        t <- lookupVariable(v)
        r <- enforceType(t, IntegerType)
      } yield r
    }
    case ReadShortIntStmt(v: String) => {
      for {
        t <- lookupVariable(v)
        r <- enforceType(t, IntegerType)
      } yield r
    }
    case ReadCharStmt(v: String) => {
      for {
        t <- lookupVariable(v)
        r <- enforceType(t, CharacterType)
      } yield r
    }
  }

  private def checkExpressions(
      exps: List[Expression]
  ): StateOrError[List[Type]] = {
    exps.foldRight[StateOrError[List[Type]]](pure(List()))((exp, acc) =>
      for {
        t <- checkExpression(exp)
        ts <- acc
      } yield (t :: ts)
    )
  }

  private def lookupProcedure(name: String): StateOrError[Procedure] =
    StateT[ErrorOr, Environment[Type], Procedure]((env: Environment[Type]) => {
      env.lookupProcedure(name) match {
        case Some(p) => Right((env, p))
        case None    => Left(s"Undefined procedure ${name}.")
      }
    })

  private def lookupVariable(name: String): StateOrError[Type] =
    StateT[ErrorOr, Environment[Type], Type]((env: Environment[Type]) => {
      env.lookup(name) match {
        case Some(t) => Right((env, t))
        case None    => Left(s"Undefined variable ${name}.")
      }
    })

  private def enforceType(at: Type, et: Type): StateOrError[Type] =
    enforceAnyType(at, List(et))

  private def enforceTypes(ts: List[Type], et: Type): StateOrError[Type] =
    ts.foldRight[StateOrError[Type]](pure(et))((t, acc) => enforceType(t, et))

  private def enforceAnyType(t: Type, ts: List[Type]): StateOrError[Type] = {
    if (ts.contains(t)) {
      pure(t)
    } else {
      assertError(s"Unexpected type ${t}.")
    }
  }

  private def checkOperation(
      lExpr: Expression,
      rExpr: Expression,
      expTypes: List[Type],
      resType: Type
  ): StateOrError[Type] = {
    for {
      t1 <- checkExpression(lExpr)
      t2 <- checkExpression(rExpr)
      t <- enforceType(t1, t2)
      _ <- enforceAnyType(t, expTypes)
    } yield resType
  }

  private def checkOperationKeepType(
      lExpr: Expression,
      rExpr: Expression,
      expTypes: List[Type]
  ): StateOrError[Type] = {
    for {
      t1 <- checkExpression(lExpr)
      t2 <- checkExpression(rExpr)
      t <- enforceType(t1, t2)
      _ <- enforceAnyType(t, expTypes)
    } yield t
  }

  private def argumentsWrongType(
      procedureName: String,
      env: Environment[Type],
      arguments: List[Expression],
      expectedArguments: List[FormalArg]
  ): Option[String] = {
    // If we return Some(err) there was an error
    // Otherwise, if we return None, there was no error

    if (arguments.length != expectedArguments.length) {
      Some(
        s"Wrong number of arguments for procedure ${procedureName}. " +
          s"Expected ${expectedArguments.length}, but got ${arguments.length}."
      )
    } else {
      // None indicates no error. Some indicates an error.
      // We start assuming no error. If we find any in the process,
      // including if there is a different type, we return it.

      // TODO: Review this implementation, seems more complex than
      // it should be

      arguments
        .zip(expectedArguments)
        .foldRight[Option[String]](None)((args, acc) => {
          acc match {
            case Some(err) => Some(err)
            case None => {
              val (arg: Expression, expArg: FormalArg) = args
              checkExpression(arg).runA(env) match {
                case Left(err) => Some(err)
                case Right(t) => {
                  if (t == expArg.argumentType) { None }
                  else {
                    Some(
                      s"Wrong argument type for procedure ${procedureName}. " +
                        s"Expected ${expArg.argumentType}, but got ${t}."
                    )
                  }
                }
              }
            }
          }
        })
    }
  }
}
