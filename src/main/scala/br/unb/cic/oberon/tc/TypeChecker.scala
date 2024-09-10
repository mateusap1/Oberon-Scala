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

  private def validOperationTypes(
      left: Type,
      right: Type,
      expected: List[Type],
      result: Type
  ): StateOrError[Type] = {
    if (left == right) {
      if (expected.contains(left)) {
        pure(result)
      } else {
        assertError(s"Type ${left} is not comparable")
      }
    } else {
      assertError(
        "Binary operation received expressions of different types"
      )
    }
  }

  private def checkOperation(
      left: Expression,
      right: Expression,
      expected: List[Type],
      result: Type
  ): StateOrError[Type] = {
    for {
      t1 <- checkExpression(left)
      t2 <- checkExpression(right)
      r <- validOperationTypes(t1, t2, expected, result)
    } yield r
  }

  private def checkOperationKeepType(
      left: Expression,
      right: Expression,
      expected: List[Type]
  ): StateOrError[Type] = {
    for {
      t1 <- checkExpression(left)
      t2 <- checkExpression(right)
      r <- validOperationTypes(t1, t2, expected, t1)
    } yield r
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

  def checkExpression(exp: Expression): StateOrError[Type] = {
    exp match {
      case IntValue(_)    => pure(IntegerType)
      case RealValue(_)   => pure(RealType)
      case CharValue(_)   => pure(CharacterType)
      case BoolValue(_)   => pure(BooleanType)
      case StringValue(_) => pure(StringType)
      case Location(_)    => pure(LocationType)
      case NullValue      => pure(NullType)
      case Undef()        => assertError("Undefined type.")
      case VarExpression(name) =>
        StateT[ErrorOr, Environment[Type], Type](env =>
          env.lookup(name) match {
            case None    => Left(s"Undefined type for variable ${name}.")
            case Some(t) => Right((env, t))
          }
        )
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
      case AndExpression(l, r) =>
        checkOperation(l, r, List(BooleanType), BooleanType)
      case OrExpression(l, r) =>
        checkOperation(l, r, List(BooleanType), BooleanType)
      case FunctionCallExpression(name: String, args: List[Expression]) =>
        StateT[ErrorOr, Environment[Type], Type]((env: Environment[Type]) => {
          // Find procedure should return an Option? Not currently the case.
          val procedure: Option[Procedure] = env.lookupProcedure(name)

          // Question of implementation. How should we handle void return types?
          // Is using UndefinedType appropriate? Should we use Null instead?
          // Is UndefinedType necessary at all?

          procedure match {
            case None => Left(s"Undeclared procedure ${name}!")
            case Some(p) => {
              argumentsWrongType(name, env, args, p.args) match {
                case None =>
                  p.returnType match {
                    case None    => Right((env, UndefinedType))
                    case Some(r) => Right((env, r))
                  }
                case Some(err) => Left(err)
              }
            }
          }

        })
      case ArrayValue(values, arrayType) =>
        StateT[ErrorOr, Environment[Type], Type]((env: Environment[Type]) => {
          val typeError = values.foldRight[Option[String]](None)(
            (exp: Expression, acc: Option[String]) => {
              acc match {
                case Some(err) => Some(err)
                case None => {
                  checkExpression(exp).runA(env) match {
                    case Left(err) => Some(err)
                    case Right(t: Type) => {
                      if (t == arrayType.baseType) { None }
                      else {
                        Some(
                          s"Element from array of wrong type. "
                            + s"Expected type ${arrayType}, but got ${t}."
                        )
                      }
                    }
                  }
                }
              }
            }
          )

          // Should we check size of array as well? Or is that guaranteed already?
          // Not checking right now: Can declare ArrayValue(
          //  ListBuffer(1, 2, 3),
          //  ArrayType(length: 42, baseType: IntegerType)
          // )
          // Meaning the list has 3 elements but length says it should have 42
          // Previous implementation did not handle that either.

          typeError match {
            case Some(err) => Left(err)
            case None      => Right((env, arrayType))
          }
        })
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

  def checkProcedure(procedure: Procedure): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  def checkStmt(stmt: Statement): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }
}
