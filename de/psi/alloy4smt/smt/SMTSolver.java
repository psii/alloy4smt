package de.psi.alloy4smt.smt;

import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;

import java.util.List;
import java.util.Vector;

public class SMTSolver implements SATSolver {
    private int numBoolVars = 0;
    private int numClauses = 0;
    private SMTFormula formula = new SMTFormula();

    @Override
    public int numberOfVariables() {
        return numBoolVars;
    }

    @Override
    public int numberOfClauses() {
        return numClauses;
    }

    @Override
    public void addVariables(int numVars) {
        numBoolVars += numVars;
        for (int i = 1; i <= numVars; ++i) {
            formula.addBoolVariable("cnf_" + i);
        }
    }

    @Override
    public boolean addClause(int[] lits) {
        List<SExpr<String>> slits = new Vector<SExpr<String>>();
        slits.add(SExpr.<String>sym("or"));
        for (int i = 0; i < lits.length; ++i) {
            if (lits[i] < 0) {
                slits.add(SExpr.call("not", SExpr.leaf("cnf_" + (-lits[i]))));
            } else {
                slits.add(SExpr.leaf("cnf_" + lits[i]));
            }
        }
        formula.addConstraint(new SExpr.SList<String>(slits));
        numClauses++;
        return false;
    }

    @Override
    public boolean solve() throws SATAbortedException {
        return false;
    }

    @Override
    public boolean valueOf(int variable) {
        return false;
    }

    @Override
    public void free() {

    }

    public SMTFormula makeSMTFormula() {
        return formula;
    }

    public void addEquality(int relvar, SExpr<String> expr) {
        formula.addConstraint(SExpr.<String>eq(SExpr.<String>leaf("cnf_" + relvar), expr));
    }

    public void addIntVariable(String name) {
        formula.addIntegerVariable(name);
    }
}
