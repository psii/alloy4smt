package de.psi.alloy4smt.ast;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.Err;


public class TranslatorTest {
	
	@Test
	public void simple() throws Err {
		final String doc = 
			"open util/intref\n" +
			"one sig X { v: Int }\n" +
			"one sig Y { u: Int }\n" +
			"fact { X.v + Y.u = 4 }\n" +
			"pred show {}\n" +
			"run show for 1\n";
		Translator.execute(doc);
	}

}
