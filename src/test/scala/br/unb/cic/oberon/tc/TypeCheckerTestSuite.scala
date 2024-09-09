package br.unb.cic.oberon.tc

import br.unb.cic.oberon.AbstractTestSuite

import java.nio.file.{Files, Paths}
import br.unb.cic.oberon.ir.ast._
import br.unb.cic.oberon.ir.ast.{
  AndExpression,
  EQExpression,
  GTEExpression,
  LTEExpression,
  LTExpression
}
import br.unb.cic.oberon.parser.ScalaParser
import br.unb.cic.oberon.parser.Oberon2ScalaParser
import org.scalatest.funsuite.AnyFunSuite
import br.unb.cic.oberon.transformations.{CoreChecker, CoreTransformer}
import br.unb.cic.oberon.ir.ast.{OberonModule, VariableDeclaration}
import br.unb.cic.oberon.environment.Environment
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.mutable.{Map, Stack, ListBuffer}

class TypeCheckerTestSuite extends AbstractTestSuite with Oberon2ScalaParser {

  test("Check expression on atomic values") {
    val atomicValues = List(
      (BoolValue(true), BooleanType),
      (IntValue(1), IntegerType),
      (RealValue(1.3), RealType),
      (CharValue('a'), CharacterType),
      (StringValue("abc"), StringType)
    )

    for ((atom, t) <- atomicValues) {
      assert(
        TypeChecker
          .checkExpression(atom)
          .runA(new Environment[Type]()) == Right(t)
      )
    }
  }

  test("Check var expression") {
    assert(
      TypeChecker
        .checkExpression(VarExpression("abc"))
        .runA(new Environment[Type]())
        .isLeft
    )

    assert(
      TypeChecker
        .checkExpression(VarExpression("abc"))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> IntegerType
            ),
            global = Map(
              "abc" -> Location(0)
            )
          )
        ) == Right(IntegerType)
    )

    assert(
      TypeChecker
        .checkExpression(VarExpression("abc"))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> IntegerType
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0)
              )
            )
          )
        ) == Right(IntegerType)
    )
  }

  test("Check comparable operations") {
    val env = new Environment[Type]()
    val correctExpressions = List(
      GTExpression(IntValue(1), IntValue(3)),
      GTExpression(RealValue(3), RealValue(1)),
      LTExpression(IntValue(1), IntValue(3)),
      LTExpression(RealValue(3), RealValue(1)),
      GTEExpression(IntValue(1), IntValue(3)),
      GTEExpression(RealValue(3), RealValue(1)),
      LTEExpression(IntValue(1), IntValue(3)),
      LTEExpression(RealValue(3), RealValue(1))
    )

    for (exp <- correctExpressions) {
      assert(
        TypeChecker
          .checkExpression(exp)
          .runA(env) == Right(BooleanType)
      )
    }

    val wrongExpressions = List(
      GTExpression(IntValue(1), RealValue(3)),
      GTExpression(RealValue(3), IntValue(1)),
      GTExpression(BoolValue(true), BoolValue(true)),
      LTExpression(IntValue(1), RealValue(3)),
      LTExpression(RealValue(3), IntValue(1)),
      LTExpression(BoolValue(true), BoolValue(true)),
      GTEExpression(IntValue(1), RealValue(3)),
      GTEExpression(RealValue(3), IntValue(1)),
      GTEExpression(BoolValue(true), BoolValue(true)),
      LTEExpression(IntValue(1), RealValue(3)),
      LTEExpression(RealValue(3), IntValue(1)),
      LTEExpression(BoolValue(true), BoolValue(true))
    )

    for (exp <- wrongExpressions) {
      assert(
        TypeChecker
          .checkExpression(exp)
          .runA(new Environment[Type]())
          .isLeft
      )
    }

    assert(
      TypeChecker
        .checkExpression(GTExpression(VarExpression("abc"), IntValue(2)))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> IntegerType
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0)
              )
            )
          )
        ) == Right(BooleanType)
    )
  }

  test("Check numeric operations") {
    val env = new Environment[Type]()
    val correctExpressions = List(
      (IntValue(1), IntValue(3), IntegerType),
      (RealValue(3), RealValue(1), RealType)
    )

    for ((l, r, t) <- correctExpressions) {
      for (
        exp <- List(
          AddExpression(l, r),
          SubExpression(l, r),
          MultExpression(l, r),
          DivExpression(l, r)
        )
      ) {
        assert(
          TypeChecker
            .checkExpression(exp)
            .runA(env) == Right(t)
        )
      }
    }

    val wrongExpressions = List(
      (IntValue(1), RealValue(3)),
      (RealValue(3), IntValue(1)),
      (BoolValue(true), BoolValue(false))
    )

    for ((l, r) <- wrongExpressions) {
      for (
        exp <- List(
          AddExpression(l, r),
          SubExpression(l, r),
          MultExpression(l, r),
          DivExpression(l, r)
        )
      ) {
        assert(TypeChecker.checkExpression(exp).runA(env).isLeft)
      }
    }

    assert(
      TypeChecker
        .checkExpression(AddExpression(VarExpression("abc"), IntValue(2)))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> IntegerType
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0)
              )
            )
          )
        ) == Right(IntegerType)
    )

    assert(
      TypeChecker
        .checkExpression(AddExpression(VarExpression("abc"), RealValue(2)))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> RealType
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0)
              )
            )
          )
        ) == Right(RealType)
    )
  }

  test("Check boolean operations") {
    val env = new Environment[Type]()

    assert(
      TypeChecker
        .checkExpression(AndExpression(BoolValue(true), BoolValue(false)))
        .runA(env) == Right(BooleanType)
    )

    assert(
      TypeChecker
        .checkExpression(OrExpression(BoolValue(true), BoolValue(false)))
        .runA(env) == Right(BooleanType)
    )

    assert(
      TypeChecker
        .checkExpression(AndExpression(IntValue(1), BoolValue(false)))
        .runA(env)
        .isLeft
    )

    assert(
      TypeChecker
        .checkExpression(OrExpression(IntValue(1), IntValue(2)))
        .runA(env)
        .isLeft
    )

    assert(
      TypeChecker
        .checkExpression(AndExpression(VarExpression("abc"), BoolValue(false)))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> BooleanType
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0)
              )
            )
          )
        ) == Right(BooleanType)
    )
  }

  test("Check function calls") {
    val env = new Environment[Type](procedures =
      Map(
        "abc" -> Procedure(
          name = "abc",
          args = List(
            ParameterByValue("a", IntegerType),
            ParameterByReference("b", BooleanType),
            ParameterByValue("c", CharacterType)
          ),
          returnType = Some(RealType),
          constants = List(),
          variables = List(),
          stmt = SequenceStmt(List())
        )
      )
    )

    assert(
      TypeChecker
        .checkExpression(
          FunctionCallExpression(
            "abc",
            List(IntValue(1), BoolValue(false), CharValue('a'))
          )
        )
        .runA(env) == Right(RealType)
    )

    assert(
      TypeChecker
        .checkExpression(
          FunctionCallExpression(
            "cde",
            List(IntValue(1), BoolValue(false), CharValue('a'))
          )
        )
        .runA(env)
        .isLeft
    )

    assert(
      TypeChecker
        .checkExpression(
          FunctionCallExpression(
            "abc",
            List(RealValue(1.0), BoolValue(false), CharValue('a'))
          )
        )
        .runA(env)
        .isLeft
    )

    assert(
      TypeChecker
        .checkExpression(
          FunctionCallExpression(
            "abc",
            List(IntValue(1), BoolValue(false), StringValue("a"))
          )
        )
        .runA(env)
        .isLeft
    )
  }

  test("Check array definition") {
    val env = new Environment[Type]()

    assert(
      TypeChecker
        .checkExpression(
          ArrayValue(
            ListBuffer(IntValue(1), IntValue(2), IntValue(3)),
            ArrayType(3, IntegerType)
          )
        )
        .runA(env) == Right(ArrayType(3, IntegerType))
    )
  }

  test("Check array subscript") {
    val env = new Environment[Type]()
    val arr = ArrayValue(
      ListBuffer(RealValue(1.0), RealValue(2.0), RealValue(3.0)),
      ArrayType(3, RealType)
    )

    assert(
      TypeChecker
        .checkExpression(ArraySubscript(arr, IntValue(0)))
        .runA(env) == Right(RealType)
    )

    assert(
      TypeChecker
        .checkExpression(ArraySubscript(arr, RealValue(0.0)))
        .runA(env)
        .isLeft
    )

    assert(
      TypeChecker
        .checkExpression(ArraySubscript(IntValue(3), RealValue(0.0)))
        .runA(env)
        .isLeft
    )
  }
}
