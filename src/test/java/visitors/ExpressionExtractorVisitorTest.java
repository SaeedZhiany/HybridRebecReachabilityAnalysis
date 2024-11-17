package visitors;

import dataStructure.*;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.*;
import org.rebecalang.compiler.modelcompiler.hybridrebeca.objectmodel.HybridTermPrimary;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class ExpressionExtractorVisitorTest {

    Literal createLiteral(Object a, String type) {
        Literal literalA = new Literal();
        literalA.setLiteralValue(String.valueOf(a));
        OrdinaryPrimitiveType typeA = new OrdinaryPrimitiveType();
        typeA.setName(type);
        literalA.setType(typeA);
        return literalA;
    }

    TermPrimary createTermPrimary(String name) {
        TermPrimary termPrimary = new TermPrimary();
        termPrimary.setName(name);
        return termPrimary;
    }

    UnaryExpression createUnaryExpression(String operator, Expression a) {
        UnaryExpression unaryExpression = new UnaryExpression();
        unaryExpression.setOperator(operator);
        unaryExpression.setExpression(a);
        return unaryExpression;
    }

    BinaryExpression creatBinaryExpression(String operator, Expression a, Expression b) {
        BinaryExpression binaryExpression = new BinaryExpression();
        binaryExpression.setOperator(operator);
        binaryExpression.setLeft(a);
        binaryExpression.setRight(b);
        return binaryExpression;
    }

    HybridTermPrimary createHybridTermPrimary(String name, int order) {
        HybridTermPrimary hybridTermPrimary = new HybridTermPrimary();
        hybridTermPrimary.setName(name);
        hybridTermPrimary.setDerivativeOrder(order);
        return hybridTermPrimary;
    }

    @Test
    @Tag("test binary expression int(literal) + int(literal)")
    void testBinaryExpressionIntLiteralPlusIntLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "+",
                createLiteral(1, "int"),
                createLiteral(2, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        System.out.println(actual);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1+2", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) + int(termPrimary)")
    void testBinaryExpressionIntLiteralPlusIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "+",
                createLiteral(1, "int"),
                createTermPrimary("a"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1+a", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(termPrimary) + int(termPrimary)")
    void testBinaryExpressionIntTermPrimaryPlusIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "+",
                createTermPrimary("a"),
                createTermPrimary("b"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("a+b", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) - int(literal)")
    void testBinaryExpressionIntLiteralMinusIntLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "-",
                createLiteral(1, "int"),
                createLiteral(2, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1-2", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) - int(termPrimary)")
    void testBinaryExpressionIntLiteralMinusIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "-",
                createLiteral(1, "int"),
                createTermPrimary("a"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1-a", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(termPrimary) - int(termPrimary)")
    void testBinaryExpressionIntTermPrimaryMinusIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "-",
                createTermPrimary("a"),
                createTermPrimary("b"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("a-b", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) * int(literal)")
    void testBinaryExpressionIntLiteralMultiplyIntLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "*",
                createLiteral(2, "int"),
                createLiteral(3, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("2*3", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) * int(termPrimary)")
    void testBinaryExpressionIntLiteralMultiplyIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "*",
                createLiteral(2, "int"),
                createTermPrimary("a"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("2*a", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(termPrimary) * int(termPrimary)")
    void testBinaryExpressionIntTermPrimaryMultiplyIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "*",
                createTermPrimary("a"),
                createTermPrimary("b"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("a*b", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) / int(literal)")
    void testBinaryExpressionIntLiteralDivideIntLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "/",
                createLiteral(6, "int"),
                createLiteral(3, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("6/3", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) / int(termPrimary)")
    void testBinaryExpressionIntLiteralDivideIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "/",
                createLiteral(6, "int"),
                createTermPrimary("a"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("6/a", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(termPrimary) / int(termPrimary)")
    void testBinaryExpressionIntTermPrimaryDivideIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "/",
                createTermPrimary("a"),
                createTermPrimary("b"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("a/b", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) % int(literal)")
    void testBinaryExpressionIntLiteralModIntLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "%",
                createLiteral(5, "int"),
                createLiteral(2, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("5%2", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) % int(termPrimary)")
    void testBinaryExpressionIntLiteralModIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "%",
                createLiteral(5, "int"),
                createTermPrimary("a"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("5%a", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(termPrimary) % int(termPrimary)")
    void testBinaryExpressionIntTermPrimaryModIntTermPrimary() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "%",
                createTermPrimary("a"),
                createTermPrimary("b"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("a%b", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression double(literal) + double(literal)")
    void testBinaryExpressionDoubleLiteralPlusDoubleLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "+",
                createLiteral(1.6, "double"),
                createLiteral(2.5, "double"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1.6+2.5", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression double(literal) - int(termPrimary)")
    void testBinaryExpressionDoubleLiteralMinusIntTermPrimary() {
        Map<String, Variable> symbolTable = new HashMap<>();
        BinaryExpression binaryExpression = creatBinaryExpression(
                "-",
                createLiteral(1.5, "double"),
                createTermPrimary("a"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1.5-a", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression boolean(literal) && boolean(literal)")
    void testBinaryExpressionBooleanLiteralAndBooleanLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "&&",
                createLiteral(true, "boolean"),
                createLiteral(false, "boolean"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("true&&false", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression boolean(literal) || boolean(literal)")
    void testBinaryExpressionBooleanLiteralOrBooleanLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "||",
                createLiteral(true, "boolean"),
                createLiteral(false, "boolean"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("true||false", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression boolean(literal) == boolean(literal)")
    void testBinaryExpressionBooleanLiteralEqualBooleanLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "==",
                createLiteral(true, "boolean"),
                createLiteral(false, "boolean"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("true==false", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) == int(literal)")
    void testBinaryExpressionIntLiteralEqualIntLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "==",
                createLiteral(1, "int"),
                createLiteral(1, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1==1", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression double(literal) == double(literal)")
    void testBinaryExpressionDoubleLiteralEqualDoubleLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "==",
                createLiteral(1.5, "double"),
                createLiteral(1.5, "double"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1.5==1.5", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression boolean(literal) != boolean(literal)")
    void testBinaryExpressionBooleanLiteralNotEqualBooleanLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "!=",
                createLiteral(true, "boolean"),
                createLiteral(false, "boolean"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("true!=false", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression int(literal) != int(literal)")
    void testBinaryExpressionIntLiteralNotEqualIntLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "!=",
                createLiteral(1, "int"),
                createLiteral(1, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1!=1", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression double(literal) != double(literal)")
    void testBinaryExpressionDoubleLiteralNotEqualDoubleLiteral() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "!=",
                createLiteral(1.5, "double"),
                createLiteral(1.5, "double"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(binaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("1.5!=1.5", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test unary expression -int(literal)")
    void testUnaryExpressionMinusIntLiteral() {
        UnaryExpression unaryExpression = createUnaryExpression("-", createLiteral(1, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(unaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("-(1)", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test unary expression +int(literal)")
    void testUnaryExpressionPlusIntLiteral() {
        UnaryExpression unaryExpression = createUnaryExpression("+", createLiteral(1, "int"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(unaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("+(1)", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test unary expression -double(literal)")
    void testUnaryExpressionMinusDoubleLiteral() {
        UnaryExpression unaryExpression = createUnaryExpression("-", createLiteral(1.5, "double"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(unaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("-(1.5)", ((StringVariable) actual).getValue());
    }

//    @Test
    @Tag("test unary expression !boolean(literal)")
    void testUnaryExpressionNotBooleanLiteral() {
        UnaryExpression unaryExpression = createUnaryExpression("!", createLiteral(true, "boolean"));
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(unaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("!(true)", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression and unary expression -(2 + 3)")
    void testBinaryExpressionAndUnaryExpression() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "+",
                createLiteral(2, "int"),
                createLiteral(3, "int"));
        UnaryExpression unaryExpression = createUnaryExpression("-", binaryExpression);
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(unaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("-(2+3)", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression and unary expression -(2 + -(3))")
    void testBinaryExpressionAndUnaryExpression2() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "+",
                createLiteral(2, "int"),
                createUnaryExpression("-", createLiteral(3, "int")));
        UnaryExpression unaryExpression = createUnaryExpression("-", binaryExpression);
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(unaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("-(2+-(3))", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test binary expression and unary expression +(-(2.5) + 3.1)")
    void testBinaryExpressionAndUnaryExpression3() {
        BinaryExpression binaryExpression = creatBinaryExpression(
                "+",
                createUnaryExpression("-", createLiteral(2.5, "double")),
                createLiteral(3.1, "double"));
        UnaryExpression unaryExpression = createUnaryExpression("+", binaryExpression);
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(unaryExpression);
        assertTrue(actual instanceof StringVariable);
        assertEquals("+(-(2.5)+3.1)", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test HybridTermPrimary order-1 time'")
    void testHybridTermPrimaryFirstOrder() {
        HybridTermPrimary hybridTermPrimary = createHybridTermPrimary(
                "time",
                1);
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(hybridTermPrimary);
        assertTrue(actual instanceof StringVariable);
        assertEquals("time'", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test HybridTermPrimary order-2 time''")
    void testHybridTermPrimarySecondOrder() {
        HybridTermPrimary hybridTermPrimary = createHybridTermPrimary(
                "time",
                2);
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        Variable actual = expressionExtractorVisitor.visit(hybridTermPrimary);
        assertTrue(actual instanceof StringVariable);
        assertEquals("time''", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test TermPrimary with setNameOfPhisicalVarible hws_time")
    void testTermPrimaryWithSetNameOfPhisicalVarible() {
        TermPrimary termPrimary = createTermPrimary("time");
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        expressionExtractorVisitor.setNameOfPhisicalVarible("hws");
        Variable actual = expressionExtractorVisitor.visit(termPrimary);
        assertTrue(actual instanceof StringVariable);
        assertEquals("hws_time", ((StringVariable) actual).getValue());
    }

    @Test
    @Tag("test HybridTermPrimary order-2 with setNameOfPhisicalVarible hws_time''")
    void testHybridTermPrimarySecondOrderWithSetNameOfPhisicalVarible() {
        HybridTermPrimary hybridTermPrimary = createHybridTermPrimary(
                "time",
                2);
        ExpressionExtractorVisitor expressionExtractorVisitor = new ExpressionExtractorVisitor();
        expressionExtractorVisitor.setNameOfPhisicalVarible("hws");
        Variable actual = expressionExtractorVisitor.visit(hybridTermPrimary);
        assertTrue(actual instanceof StringVariable);
        assertEquals("hws_time''", ((StringVariable) actual).getValue());
    }
}