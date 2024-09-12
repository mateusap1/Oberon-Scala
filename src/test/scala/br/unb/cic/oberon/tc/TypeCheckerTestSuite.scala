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

class TypeCheckerTestSuite extends AnyFunSuite with Oberon2ScalaParser {

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

  test("Check pointer access") {
    val env = new Environment[Type](
      locations = Map(
        Location(0) -> PointerType(IntegerType)
      ),
      stack = Stack(
        Map(
          "abc" -> Location(0)
        )
      )
    )

    assert(
      TypeChecker
        .checkExpression(PointerAccessExpression("abc"))
        .runA(env) == Right(IntegerType)
    )
  }

  test("Check lambda expression") {
    val env = new Environment[Type]()

    assert(
      TypeChecker
        .checkExpression(
          LambdaExpression(
            List(
              ParameterByReference("x", IntegerType),
              ParameterByReference("y", IntegerType)
            ),
            GTExpression(VarExpression("x"), VarExpression("y"))
          )
        )
        .runA(env) == Right(BooleanType)
    )

    assert(
      TypeChecker
        .checkExpression(
          LambdaExpression(
            List(
              ParameterByReference("x", IntegerType),
              ParameterByReference("y", IntegerType)
            ),
            GTExpression(VarExpression("x"), VarExpression("z"))
          )
        )
        .runA(env)
        .isLeft
    )
  }

  test("Check assignment stmts") {
    // Can't test records currently

    assert(
      TypeChecker
        .checkStmt(AssignmentStmt(VarAssignment("abc"), RealValue(0.0)))
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
        ) == Right(NullType)
    )

    assert(
      TypeChecker
        .checkStmt(AssignmentStmt(VarAssignment("abc"), IntValue(0)))
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
        )
        .isLeft
    )

    assert(
      TypeChecker
        .checkStmt(
          AssignmentStmt(
            ArrayAssignment(
              ArrayValue(ListBuffer(), ArrayType(3, RealType)),
              IntValue(0)
            ),
            RealValue(0.0)
          )
        )
        .runA(new Environment[Type]()) == Right(NullType)
    )

    assert(
      TypeChecker
        .checkStmt(
          AssignmentStmt(
            ArrayAssignment(
              ArrayValue(ListBuffer(), ArrayType(3, CharacterType)),
              IntValue(0)
            ),
            RealValue(0.0)
          )
        )
        .runA(new Environment[Type]())
        .isLeft
    )

    assert(
      TypeChecker
        .checkStmt(AssignmentStmt(PointerAssignment("abc"), RealValue(0.0)))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> PointerType(RealType)
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0)
              )
            )
          )
        ) == Right(NullType)
    )

    assert(
      TypeChecker
        .checkStmt(AssignmentStmt(PointerAssignment("abc"), RealValue(0.0)))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> PointerType(IntegerType)
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0)
              )
            )
          )
        )
        .isLeft
    )
  }

  test("Check sequence stmt") {
    assert(
      TypeChecker
        .checkStmt(
          SequenceStmt(
            List(
              AssignmentStmt(VarAssignment("abc"), RealValue(0.0)),
              AssignmentStmt(VarAssignment("abc"), RealValue(1.0)),
              AssignmentStmt(VarAssignment("bcd"), IntValue(0))
            )
          )
        )
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> RealType,
              Location(1) -> IntegerType
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0),
                "bcd" -> Location(1)
              )
            )
          )
        ) == Right(NullType)
    )

    assert(
      TypeChecker
        .checkStmt(
          SequenceStmt(
            List(
              AssignmentStmt(VarAssignment("abc"), RealValue(0.0)),
              AssignmentStmt(VarAssignment("abc"), RealValue(1.0)),
              AssignmentStmt(VarAssignment("bcd"), IntValue(0))
            )
          )
        )
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> RealType,
              Location(1) -> IntegerType
            ),
            stack = Stack(
              Map(
                "abc" -> Location(0)
              )
            )
          )
        )
        .isLeft
    )
  }

  test("Check read stmts") {
    assert(
      TypeChecker
        .checkStmt(ReadLongRealStmt("abc"))
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
        ) == Right(NullType)
    )

    assert(
      TypeChecker
        .checkStmt(ReadLongRealStmt("abc"))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> RealType
            ),
            global = Map(
              "abc" -> Location(0)
            )
          )
        ) == Right(NullType)
    )

    assert(
      TypeChecker
        .checkStmt(ReadLongRealStmt("abc"))
        .runA(new Environment[Type]())
        .isLeft
    )

    assert(
      TypeChecker
        .checkStmt(ReadLongRealStmt("abc"))
        .runA(
          new Environment[Type](
            locations = Map(
              Location(0) -> IntegerType
            ),
            global = Map(
              "abc" -> Location(0)
            )
          )
        )
        .isLeft
    )
  }

  test("Check write stmt") {
    val env = new Environment[Type]()

    assert(
      TypeChecker
        .checkStmt(WriteStmt(IntValue(1)))
        .runA(env) == Right(NullType)
    )
  }

  // ------

  test("Test read int statement type checker") {
    val env = new Environment[Type]()
      .setGlobalVariable("x", IntegerType)
      .setGlobalVariable("y", IntegerType)
    val read01 = ReadIntStmt("x")
    val read02 = ReadIntStmt("y")

    assert(TypeChecker.checkStmt(read01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(read02).runA(env) == Right(NullType))
  }

  test("Test read real statement type checker") {
    val env = new Environment[Type]().setGlobalVariable("x", RealType)
    val read01 = ReadRealStmt("x")
    val read02 = ReadRealStmt("y")

    assert(TypeChecker.checkStmt(read01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(read02).runA(env).isLeft)
  }

  test("Test write statement type checker") {
    val env = new Environment[Type]()
    val write01 = WriteStmt(IntValue(5))
    val write02 = WriteStmt(AddExpression(IntValue(5), BoolValue(false)))

    assert(TypeChecker.checkStmt(write01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(write02).runA(env).isLeft)
  }

  test("Test assignment statement type checker") {
    val env = new Environment[Type]().setGlobalVariable("x", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 =
      AssignmentStmt(VarAssignment("y"), IntValue(10)) // invalid stmt
    val stmt03 = AssignmentStmt(
      VarAssignment("x"),
      AddExpression(IntValue(5), BoolValue(false))
    )

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt03).runA(env).isLeft)
  }

  test("Test a sequence of statements type checker") {
    val env = new Environment[Type]().setGlobalVariable("x", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 =
      AssignmentStmt(VarAssignment("y"), IntValue(10)) // invalid stmt
    val stmt03 = AssignmentStmt(
      VarAssignment("x"),
      AddExpression(IntValue(5), BoolValue(false))
    ) // invalid stmt
    val stmt04 = WriteStmt(VarExpression("x"))
    val stmt05 = WriteStmt(VarExpression("y"))

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt03).runA(env).isLeft)

    val seq1 = SequenceStmt(List(stmt01, stmt04))
    val seq2 = SequenceStmt(List(stmt01, stmt05))

    assert(TypeChecker.checkStmt(seq1).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(seq2).runA(env).isLeft)
  }

  test("Test if-else statement type checker (with invalid condition)") {
    val env = new Environment[Type]().setGlobalVariable("x", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 = IfElseStmt(IntValue(10), stmt01, None)

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
  }

  test("Test if-else statement type checker (with invalid then-stmt)") {
    val env = new Environment[Type]()
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 = IfElseStmt(BoolValue(true), stmt01, None)

    assert(TypeChecker.checkStmt(stmt01).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
  }

  test(
    "Test if-else statement type checker (with invalid then-stmt and else-stmt)"
  ) {
    val env = new Environment[Type]()
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 = AssignmentStmt(VarAssignment("y"), IntValue(10))
    val stmt03 = IfElseStmt(BoolValue(true), stmt01, Some(stmt02))

    assert(TypeChecker.checkStmt(stmt01).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt03).runA(env).isLeft)
  }

  test("Test if-else statement type checker") {
    val env = new Environment[Type]()
      .setGlobalVariable("x", IntegerType)
      .setGlobalVariable("y", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 = AssignmentStmt(VarAssignment("y"), IntValue(10))
    val stmt03 = IfElseStmt(BoolValue(true), stmt01, Some(stmt02))

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt03).runA(env) == Right(NullType))
  }

  test("Test if-else-if statment type checker (invalid condition 'if')") {
    val env = new Environment[Type]()
      .setGlobalVariable("x", IntegerType)
      .setGlobalVariable("z", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(20))
    val stmt02 = AssignmentStmt(VarAssignment("z"), IntValue(30))

    val stmt03 = ElseIfStmt(BoolValue(true), stmt02)
    val list1 = List(stmt03)

    val stmt04 = CoreTransformer.reduceToCoreStatement(
      IfElseIfStmt(IntValue(34), stmt01, list1, None)
    )

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt04).runA(env).isLeft)
  }

  test("Test else-if statment type checker (invalid condition 'else-if')") {
    val env = new Environment[Type]()
      .setGlobalVariable("x", IntegerType)
      .setGlobalVariable("z", IntegerType)

    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(40))
    val stmt02 = AssignmentStmt(VarAssignment("z"), IntValue(100))

    val stmt03 = ElseIfStmt(IntValue(70), stmt02)
    val list1 = List(stmt03)

    val stmt04 = CoreTransformer.reduceToCoreStatement(
      IfElseIfStmt(BoolValue(true), stmt01, list1, None)
    )

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt04).runA(env).isLeft)
  }

  test(
    "Test else-if statment type checker (invalid condition list 'else-if')"
  ) {
    val env = new Environment[Type]()
      .setGlobalVariable("x", IntegerType)
      .setGlobalVariable("z", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(40))
    val stmt02 = AssignmentStmt(VarAssignment("z"), IntValue(100))

    val stmt03 = ElseIfStmt(BoolValue(true), stmt02)
    val stmt04 = ElseIfStmt(IntValue(73), stmt02)
    val stmt05 = ElseIfStmt(IntValue(58), stmt01)
    val stmt06 = ElseIfStmt(BoolValue(false), stmt01)
    val list1 = List(stmt03, stmt04, stmt05, stmt06)

    val stmt07 = CoreTransformer.reduceToCoreStatement(
      IfElseIfStmt(BoolValue(true), stmt01, list1, None)
    )

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt07).runA(env).isLeft)
  }

  test("Test else-if statment type checker (invalid then-stmt 'else-if')") {
    val env = new Environment[Type]().setGlobalVariable("x", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(40))
    val stmt02 = AssignmentStmt(VarAssignment("z"), IntValue(100))

    val stmt03 = ElseIfStmt(BoolValue(true), stmt02)
    val list1 = List(stmt03)

    val stmt04 = CoreTransformer.reduceToCoreStatement(
      IfElseIfStmt(BoolValue(true), stmt01, list1, None)
    )

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt04).runA(env).isLeft)
  }

  test("Test if-else-if statment type checker (invalid else-stmt)") {
    val env = new Environment[Type]()
      .setGlobalVariable("x", IntegerType)
      .setGlobalVariable("z", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(40))
    val stmt02 = AssignmentStmt(VarAssignment("z"), IntValue(100))
    val stmt03 = AssignmentStmt(VarAssignment("w"), IntValue(20))

    val stmt04 = ElseIfStmt(BoolValue(true), stmt02)
    val list1 = List(stmt04)

    val stmt05 = CoreTransformer.reduceToCoreStatement(
      IfElseIfStmt(BoolValue(true), stmt01, list1, Some(stmt03))
    )

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt03).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt05).runA(env).isLeft)
  }

  test(
    "Test if-else-if statment type checker (invalid then-stmt, 'else-if' then-stmt, 'else-if' invalid condition and else-stmt)"
  ) {
    val env = new Environment[Type]()
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(40))
    val stmt02 = AssignmentStmt(VarAssignment("z"), IntValue(100))
    val stmt03 = AssignmentStmt(VarAssignment("w"), IntValue(20))

    val stmt04 = ElseIfStmt(IntValue(56), stmt02)
    val stmt05 = ElseIfStmt(IntValue(79), stmt01)
    val stmt06 = ElseIfStmt(BoolValue(true), stmt02)
    val list1 = List(stmt04, stmt05, stmt06)

    val stmt07 = CoreTransformer.reduceToCoreStatement(
      IfElseIfStmt(BoolValue(true), stmt01, list1, Some(stmt03))
    )

    assert(TypeChecker.checkStmt(stmt01).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt03).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt07).runA(env).isLeft)
  }

  test("Test if-else-if statment type checker") {
    val env = new Environment[Type]().setGlobalVariable("x", IntegerType).setGlobalVariable("y", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(15))
    val stmt02 = AssignmentStmt(VarAssignment("y"), IntValue(5))

    val stmt03 = ElseIfStmt(BoolValue(true), stmt02)
    val list1 = List(stmt03)

    val stmt04 = CoreTransformer.reduceToCoreStatement(
      IfElseIfStmt(BoolValue(true), stmt01, list1, None)
    )

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt04).runA(env) == Right(NullType))
  }

  test("Test while statement type checker (with invalid condition)") {
    val env = new Environment[Type]().setGlobalVariable("x", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 = WhileStmt(IntValue(10), stmt01)

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
  }

  test("Test while statement type checker (with invalid stmt)") {
    val env = (new Environment[Type]())
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 = WhileStmt(BoolValue(true), stmt01)

    assert(TypeChecker.checkStmt(stmt01).runA(env).isLeft)
    assert(TypeChecker.checkStmt(stmt02).runA(env).isLeft)
  }

  test("Test while statement type checker") {
    val env = (new Environment[Type]()).setGlobalVariable("x", IntegerType)
    val stmt01 = AssignmentStmt(VarAssignment("x"), IntValue(10))
    val stmt02 = WhileStmt(BoolValue(true), stmt01)

    assert(TypeChecker.checkStmt(stmt01).runA(env) == Right(NullType))
    assert(TypeChecker.checkStmt(stmt02).runA(env) == Right(NullType))
  }

  // Was here

  test("Test EAssignment") {
    val env = new Environment[Type]()
      .addUserDefinedType(
        UserDefinedType(
          "customType",
          RecordType(List(VariableDeclaration("x1", RealType)))
        )
      )
      .setGlobalVariable("x", IntegerType)
      .setGlobalVariable("b", PointerType(BooleanType))
      .setGlobalVariable("arr", ArrayType(3, CharacterType))
      .setGlobalVariable(
        "rec",
        RecordType(List(VariableDeclaration("x", StringType)))
      )
      .setGlobalVariable(
        "userDefType",
        ReferenceToUserDefinedType("customType")
      )

    val stmt01 = new AssignmentStmt(VarAssignment("x"), IntValue(0))
    val stmt02 = new AssignmentStmt(PointerAssignment("b"), BoolValue(false))
    val stmt03 = new AssignmentStmt(
      ArrayAssignment(VarExpression("arr"), IntValue(0)),
      CharValue('a')
    )
    val stmt04 = new AssignmentStmt(
      RecordAssignment(VarExpression("rec"), "x"),
      StringValue("teste")
    )
    val stmt05 = new AssignmentStmt(
      RecordAssignment(VarExpression("userDefType"), "x1"),
      RealValue(6.9)
    )

    val stmts = SequenceStmt(List(stmt01, stmt02, stmt03, stmt04))

    assert(TypeChecker.checkStmt(stmts).runA(env) == Right(NullType))
  }

  test("Test EAssignment, PointerAssignment, missing variable") {
    val env = new Environment[Type]()
    val stmt = AssignmentStmt(PointerAssignment("b"), BoolValue(false))

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, PointerAssignment, left side not PointerType") {
    val env = new Environment[Type]().setGlobalVariable("b", IntegerType)
    val stmt = AssignmentStmt(PointerAssignment("b"), BoolValue(false))

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, PointerAssignment, invalid left side Type") {
    val env =
      new Environment[Type]().setGlobalVariable("b", PointerType(UndefinedType))
    val stmt = AssignmentStmt(PointerAssignment("b"), BoolValue(false))

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, PointerAssignment, wrong right side Type") {
    val env =
      new Environment[Type]().setGlobalVariable("b", PointerType(IntegerType))
    val stmt = AssignmentStmt(PointerAssignment("b"), BoolValue(false))

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, ArrayAssignment, wrong array type") {
    val env = new Environment[Type]().setGlobalVariable("arr", IntegerType)
    val stmt = AssignmentStmt(
      ArrayAssignment(VarExpression("arr"), IntValue(0)),
      CharValue('a')
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, ArrayAssignment, wrong index type") {
    val env = new Environment[Type]()
      .setGlobalVariable("arr", ArrayType(3, CharacterType))
    val stmt = AssignmentStmt(
      ArrayAssignment(VarExpression("arr"), BoolValue(true)),
      CharValue('a')
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, ArrayAssignment, missing array type") {
    val env = new Environment[Type]()
    val stmt = AssignmentStmt(
      ArrayAssignment(VarExpression("arr"), IntValue(0)),
      CharValue('a')
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, ArrayAssignment, missing index type") {
    val env = new Environment[Type]()
      .setGlobalVariable("arr", ArrayType(3, CharacterType))
    val stmt = AssignmentStmt(
      ArrayAssignment(VarExpression("arr"), VarExpression("i")),
      CharValue('a')
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, ArrayAssignment, wrong array element type") {
    val env = new Environment[Type]()
      .setGlobalVariable("arr", ArrayType(3, IntegerType))
    val stmt = AssignmentStmt(
      ArrayAssignment(VarExpression("arr"), IntValue(0)),
      CharValue('a')
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, RecordAssignment(RecordType), missing attribute") {
    val env = new Environment[Type]().setGlobalVariable(
      "rec",
      RecordType(List(VariableDeclaration("x", StringType)))
    )
    val stmt = AssignmentStmt(
      RecordAssignment(VarExpression("rec"), "404"),
      StringValue("teste")
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test("Test EAssignment, RecordAssignment(RecordType), wrong attribute type") {
    val env = new Environment[Type]().setGlobalVariable(
      "rec",
      RecordType(List(VariableDeclaration("x", StringType)))
    )
    val stmt = AssignmentStmt(
      RecordAssignment(VarExpression("rec"), "x"),
      IntValue(8)
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test(
    "Test EAssignment, RecordAssignment(ReferenceToUserDefinedType), missing custom type"
  ) {
    val env = new Environment[Type]().setGlobalVariable(
      "userDefType",
      ReferenceToUserDefinedType("customType")
    )
    val stmt = AssignmentStmt(
      RecordAssignment(VarExpression("userDefType"), "x"),
      RealValue(3.0)
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test(
    "Test EAssignment, RecordAssignment(ReferenceToUserDefinedType), missing attribute type"
  ) {
    val env = new Environment[Type]()
      .addUserDefinedType(
        UserDefinedType(
          "customType",
          RecordType(List(VariableDeclaration("x1", RealType)))
        )
      )
      .setGlobalVariable(
        "userDefType",
        ReferenceToUserDefinedType("customType")
      )
    val stmt = AssignmentStmt(
      RecordAssignment(VarExpression("userDefType"), "404"),
      RealValue(3.0)
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }

  test(
    "Test EAssignment, RecordAssignment(ReferenceToUserDefinedType), wrong attribute type"
  ) {
    val env = new Environment[Type]()
      .addUserDefinedType(
        UserDefinedType(
          "customType",
          RecordType(List(VariableDeclaration("x1", RealType)))
        )
      )
      .setGlobalVariable(
        "userDefType",
        ReferenceToUserDefinedType("customType")
      )
    val stmt = AssignmentStmt(
      RecordAssignment(VarExpression("userDefType"), "x1"),
      IntValue(3)
    )

    assert(TypeChecker.checkStmt(stmt).runA(env).isLeft)
  }
}
