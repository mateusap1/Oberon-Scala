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
      case FunctionCallExpression(name, args) =>
        StateT[ErrorOr, Environment[Type], Type](env => {
          // Find procedure should return an Option? Not currently the case.
          val procedure = env.findProcedure(name)

          if (args.length != procedure.args.length) {
            Left(
              s"Wrong number of arguments for procedure ${name}. Expected ${procedure.args.length} but got ${args.length}."
            )
          } else {
            // Make sure all arguments are from the correct type

            args
              .zip(procedure.args)
              .foldRight[ErrorOr[(Environment[Type], Type)]](
                Right((env, procedure.returnType.getOrElse(UndefinedType)))
              )((arg, acc) => {
                val (exp, fa) = arg

                checkExpression(exp).runA(env) match {
                  case Left(err) => Left(err)
                  case Right(t) => {
                    if (t == fa.argumentType) { acc }
                    else {
                      Left(
                        s"Wrong argument type for procedure ${name}. Expected ${fa.argumentType} but got ${t}."
                      )
                    }
                  }
                }
              })
          }
        })
      case ArrayValue(values, arrayType) => assertError("Not implemented yet.")
      case ArraySubscript(array, index)  => assertError("Not implemented yet.")
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
