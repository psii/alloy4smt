package de.psi.alloy4smt.hysat;

import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;

public class HysatSolver implements SATSolver {
	
	private int numclauses;
	private int maxlabel;
	private StringBuilder cnfbuilder;
	
	public HysatSolver() {
		numclauses = 0;
		maxlabel = 0;
		cnfbuilder = new StringBuilder();
	}

	@Override
	public int numberOfVariables() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public int numberOfClauses() {
		return numclauses;
	}

	@Override
	public void addVariables(int numVars) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean addClause(int[] lits) {
		numclauses++;
		cnfbuilder.append("\t");
		
		for (int i = 0; i < lits.length; ++i) {
			final int l = Math.abs(lits[i]);
			maxlabel = l > maxlabel ? l : maxlabel;
			if (i > 0) cnfbuilder.append(" or ");
			if (lits[i] < 0) cnfbuilder.append("!");
			cnfbuilder.append("cnf_");
			cnfbuilder.append(l);
		}
		
		cnfbuilder.append(";\n");
		
		return true;
	}

	@Override
	public boolean solve() throws SATAbortedException {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean valueOf(int variable) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void free() {
		// TODO Auto-generated method stub

	}

	public String toHysat() {
		StringBuilder result = new StringBuilder();
		
		result.append("DECL\n");
		for (int i = 1; i <= maxlabel; ++i) {
			result.append("\tboole cnf_");
			result.append(i);
			result.append(";\n");
		}
		
		result.append("EXPR\n");
		result.append(cnfbuilder);
		
		return result.toString();
	}

}
