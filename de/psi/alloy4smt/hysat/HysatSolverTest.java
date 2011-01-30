package de.psi.alloy4smt.hysat;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;


public class HysatSolverTest {
	
	@Test
	public void simple() {
		HysatSolver solver = new HysatSolver();
		boolean b;
		
		b = solver.addClause(new int[] {1, 2, 3});
		assertTrue(b);
		assertEquals(1, solver.numberOfClauses());
		
		b = solver.addClause(new int[] { 1, 3, -4 });
		assertTrue(b);
		assertEquals(2, solver.numberOfClauses());
		
		final String hysat = 
			"DECL\n" +
			"\tboole cnf_1;\n" +
			"\tboole cnf_2;\n" +
			"\tboole cnf_3;\n" +
			"\tboole cnf_4;\n" +
			"EXPR\n" +
			"\tcnf_1 or cnf_2 or cnf_3;\n" +
			"\tcnf_1 or cnf_3 or !cnf_4;\n";
		assertEquals(hysat, solver.toHysat());
		
	}

}
