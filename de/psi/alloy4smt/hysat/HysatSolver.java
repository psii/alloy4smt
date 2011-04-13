package de.psi.alloy4smt.hysat;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Vector;

import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;

public class HysatSolver implements SATSolver {
	
	private int numclauses;
	private int numvars;
	private int maxlabel;
	private StringBuilder cnfbuilder;
	private StringBuilder hyexprbuilder;
	private List<Hyvar> hyvars;
	private File output;
	
	static private class Hyvar {
		public final int min;
		public final int max;
		public final String name;
		
		public Hyvar(String name, int min, int max) {
			this.min = min;
			this.max = max;
			this.name = name;
		}
	}
	
	public HysatSolver() {
		numclauses = 0;
		numvars = 0;
		maxlabel = 0;
		cnfbuilder = new StringBuilder();
		hyexprbuilder = new StringBuilder();
		hyvars = new Vector<Hyvar>();
		output = null;
	}

	@Override
	public int numberOfVariables() {
		return numvars;
	}

	@Override
	public int numberOfClauses() {
		return numclauses;
	}

	@Override
	public void addVariables(int numVars) {
		if (numVars < 0) throw new IllegalArgumentException();
		this.numvars += numVars;
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
		try {
			output = File.createTempFile("a4smt", ".hy");
			FileWriter writer = new FileWriter(output);
			writer.write(toHysat());
			writer.close();
		} catch (IOException e) {
		}
		return true;
	}

	@Override
	public boolean valueOf(int variable) {
		return false;
	}

	@Override
	public void free() {
	}

	public String toHysat() {
		StringBuilder result = new StringBuilder();
		
		result.append("DECL\n");
		if (numvars > 0) {
			result.append("\t-- Number of input vars: ");
			result.append(numvars);
			result.append("\n");
		}
		for (int i = 1; i <= maxlabel; ++i) {
			result.append("\tboole cnf_");
			result.append(i);
			result.append(";\n");
		}
		for (Hyvar var : hyvars) {
			result.append("\tint [");
			result.append(var.min);
			result.append(", ");
			result.append(var.max);
			result.append("] ");
			result.append(var.name);
			result.append(";\n");
		}
		
		result.append("EXPR\n");
		result.append(cnfbuilder);
		result.append(hyexprbuilder);
		
		return result.toString();
	}

	public void addHysatVariable(String varname, int min, int max) {
		hyvars.add(new Hyvar(varname.replace('$', '_'), min, max));
	}

	public void addHysatExpr(String expr) {
		hyexprbuilder.append("\t");
		hyexprbuilder.append(expr.replace('$', '_'));
		hyexprbuilder.append(";\n");
	}

	public File getHysatFile() {
		return output;
	}

}
