package de.psi.alloy4smt.smt;

import org.junit.Test;

import static org.junit.Assert.*;

public class SMTFormulaTest {
    @Test
    public void simple() {
        SMTFormula form = new SMTFormula();
        assertEquals(
                "(set-logic QF_NRA)\n" +
                "(set-info :smt-lib-version 2.0)\n", form.toString());
    }

    @Test
    public void constraints() {
        SMTFormula form = new SMTFormula();
        SExpr<String> c = SExpr.call("=", SExpr.<String>num(5), SExpr.add(SExpr.<String>num(2), SExpr.<String>num(3)));
        form.addConstraint(c);
        assertEquals(
                "(set-logic QF_NRA)\n" +
                "(set-info :smt-lib-version 2.0)\n" +
                "(assert (= 5 (+ 2 3)))\n", form.toString());
    }

    @Test
    public void variables() {
        SMTFormula form = new SMTFormula();
        form.addBoolVariable("super");
        form.addIntegerVariable("duper");
        SExpr<String> c = SExpr.call("=", SExpr.leaf("super"), SExpr.call("=", SExpr.leaf("duper"), SExpr.<String>num(1)));
        form.addConstraint(c);
        assertEquals("(declare-fun super () Bool)\n" +
                "(declare-fun duper () Int)\n", form.getVariableDecls());
        assertEquals("(assert (= super (= duper 1)))\n", form.getConstraints());
        assertEquals("(set-logic QF_NRA)\n" +
                "(set-info :smt-lib-version 2.0)\n" +
                "(declare-fun super () Bool)\n" +
                "(declare-fun duper () Int)\n" +
                "(assert (= super (= duper 1)))\n", form.toString());
    }
}