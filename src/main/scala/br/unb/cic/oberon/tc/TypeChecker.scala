package br.unb.cic.oberon.tc

import br.unb.cic.oberon.tc.StateOrErrorMonad._

import br.unb.cic.oberon.ir.ast._
import br.unb.cic.oberon.environment.Environment
import br.unb.cic.oberon.visitor.OberonVisitorAdapter

import cats.data.State
import cats.data.StateT

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

          typeError match {
            case Some(err) => Left(err)
            case None      => Right((env, arrayType))
          }
        })
      case ArraySubscript(array, index) => assertError("Not implemented yet.")
      case FieldAccessExpression(exp, attributeName) =>
        assertError("Not implemented yet.")
      case PointerAccessExpression(name) => assertError("Not implemented yet.")
      case LambdaExpression(args, exp)   => assertError("Not implemented yet.")
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
