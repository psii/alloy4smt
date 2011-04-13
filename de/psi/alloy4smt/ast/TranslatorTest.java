package de.psi.alloy4smt.ast;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.Err;


public class TranslatorTest {
	
	@Test
	public void simple() throws Err {
		final String doc = 
			"open util/intref\n" +
			"sig X { v: Int }\n" +
			"sig Y { u: Int }\n" +
			"fact { all x: X { no y: Y | int(x.v) + int(y.u) = 4 } }\n" +
			"pred show {}\n" +
			"run show for 3\n";
		HyTranslator.execute(doc);
	}

}
