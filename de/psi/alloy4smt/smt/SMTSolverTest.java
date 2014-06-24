package de.psi.alloy4smt.smt;

import org.junit.Test;

import static org.junit.Assert.*;

public class SMTSolverTest {
    @Test
    public void simple() {
        SMTSolver solver = new SMTSolver();
        solver.addVariables(3);
        assertEquals(3, solver.numberOfVariables());
        assertEquals(
                "(declare-fun cnf_1 () Bool)\n" +
                "(declare-fun cnf_2 () Bool)\n" +
                "(declare-fun cnf_3 () Bool)\n", solver.makeSMTFormula().getVariableDecls());
        solver.addClause(new int[]{ 1, -3, 2 });
        solver.addClause(new int[]{ 3, -2});
        assertEquals(
                "(assert (or cnf_1 (not cnf_3) cnf_2))\n" +
                "(assert (or cnf_3 (not cnf_2)))\n", solver.makeSMTFormula().getConstraints());
        assertEquals(2, solver.numberOfClauses());
    }
}