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
        assertError("Not implemented yet.")
      case ArrayValue(values, arrayType) => assertError("Not implemented yet.")
      case ArraySubscript(array, index)  => assertError("Not implemented yet.")
      case FieldAccessExpression(exp, attributeName) =>
        assertError("Not implemented yet.")
      case PointerAccessExpression(name) => assertError("Not implemented yet.")
      case LambdaExpression(args, exp)   => assertError("Not implemented yet.")

      //   case FunctionCallExpression(name, args) => { env =>
      //     {
      //       val procedure = env.findProcedure(name)

      //       // Verificar tipos de cada argumento
      //       val errorIfExists = args.foldRight(
      //         Option[String],
      //         { (exp, acc) =>
      //           for {
      //             _ <- acc
      //             r <- checkExpression(exp).runA(env) match {
      //               case Left(err) => Some(err)
      //               case Right(_)  => None
      //             }
      //           } yield r
      //         }
      //       )

      //     }
      //   }
    }
  }

  // O checkModule deverá ser parte do construtor da classe
  def checkModule(module: OberonModule): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  def checkProcedure(procedure: Procedure): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  // Responsável por retornar as mensagens de erro
  def checkStmt(stmt: Statement): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  private def checkAssignment(stmt: Statement): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  private def checkVarAssigment(
      v: String,
      exp: Expression
  ): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  private def checkPointerAssigment(
      v: String,
      exp: Expression
  ): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  private def checkArrayAssigment(
      arr: Expression,
      element: Expression,
      exp: Expression
  ): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  private def checkRecordAssigment(
      record: Expression,
      field: String,
      exp: Expression
  ): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  private def visitIfElseStmt(stmt: Statement): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  private def visitWhileStmt(stmt: Statement): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  def visitForEachStmt(forEachStmt: ForEachStmt): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }

  private def visitExitStmt(): StateOrError[Type] = assertError(
    "Not Implemented Yet"
  )

  /*
   * Type checker for a procedure call. This is the "toughest" implementation
   * here. We have to check:
   *
   * (a) the procedure exists
   * (b) the type of the actual arguments match the type of the formal arguments
   * (c) the procedure body (stmt) is well typed.
   *
   * @param stmt (a procedure call)
   *
   * @return Our error representation (statement + string with the error message)
   */
  private def procedureCallStmt(stmt: Statement): StateOrError[Type] = {
    assertError("Not Implemented Yet")
  }
}
