package de.psi.alloy4smt.smt;

import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;

public class SMTSolver implements SATSolver {
    @Override
    public int numberOfVariables() {
        return 0;
    }

    @Override
    public int numberOfClauses() {
        return 0;
    }

    @Override
    public void addVariables(int numVars) {

    }

    @Override
    public boolean addClause(int[] lits) {
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
}
