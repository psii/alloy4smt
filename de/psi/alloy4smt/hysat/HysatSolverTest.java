package de.psi.alloy4smt.hysat;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

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
	
	@Test
	public void intvariables() {
		HysatSolver solver = new HysatSolver();
		
		solver.addHysatVariable("lala", -1000, 1000);
		solver.addHysatVariable("abc$3", 4, 2030);
		
		assertEquals(
				"DECL\n" +
				"\tint [-1000, 1000] lala;\n" +
				"\tint [4, 2030] abc_3;\n" +
				"EXPR\n", 
				solver.toHysat());
	}
	
	@Test
	public void expressions() {
		HysatSolver solver = new HysatSolver();
		
		solver.addHysatExpr("a * a + b * b = c * c");
		solver.addHysatExpr("cnf -> {x + a$4 = z$3}");
		
		assertEquals(
				"DECL\n" +
				"EXPR\n" +
				"\ta * a + b * b = c * c;\n" +
				"\tcnf -> {x + a_4 = z_3};\n",
				solver.toHysat());
	}
	
	@Test
	public void inputvars() {
		HysatSolver solver = new HysatSolver();
		
		solver.addVariables(20);
		solver.addVariables(3);
		assertEquals(23, solver.numberOfVariables());
		
		solver.addClause(new int[] {-1, 2, 3});
		
		assertEquals(
				"DECL\n" +
				"\t-- Number of input vars: 23\n" +
				"\tboole cnf_1;\n" +
				"\tboole cnf_2;\n" +
				"\tboole cnf_3;\n" +
				"EXPR\n" +
				"\t!cnf_1 or cnf_2 or cnf_3;\n",
				solver.toHysat());
	}
	
	@Test
	public void mkhysatfile() throws IOException {
		HysatSolver solver = new HysatSolver();
		
		assertNull(solver.getHysatFile());
		boolean r = solver.solve();
		
		assertTrue(r);
		assertNotNull(solver.getHysatFile());
		assertTrue(solver.getHysatFile().exists());
		
		StringBuilder sb = new StringBuilder();
		BufferedReader br = new BufferedReader(new FileReader(solver.getHysatFile()));
		while (br.ready()) { sb.append(br.readLine()); sb.append("\n"); }
		br.close();
		
		assertEquals(solver.toHysat(), sb.toString());
		assertTrue(solver.getHysatFile().delete());
	}

}
