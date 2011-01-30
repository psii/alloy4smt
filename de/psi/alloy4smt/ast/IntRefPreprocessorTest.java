package de.psi.alloy4smt.ast;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;

/**
 * Created by IntelliJ IDEA.
 * User: psi
 * Date: 10.01.11
 * Time: 15:42
 * To change this template use File | Settings | File Templates.
 */
public class IntRefPreprocessorTest {

    private static final String simpleModuleDoc =
            "sig X { v: Y }\n" +
            "sig Y { w: X ->one X }\n";

/*    private static final String doc2 =
            "sig X { v: Int }\n" +
            "sig Y { w: X ->one Int }\n";*/

    private static final String intrefmod =
            "module util/intref\n" +
            "abstract sig IntRef { aqclass: IntRef }\n";

    private static final String[] stdsigs = { "univ", "Int", "seq/Int", "String", "none" };

    private CompModule module;
    private IntRefPreprocessor.SigBuilder sigbuilder;
    private IntRefPreprocessor ppresult;

    @Before
    public void setUp() {
        module = null;
        ppresult = null;
        
        sigbuilder = new IntRefPreprocessor.SigBuilder() {
        	private int id = 1;
			@Override
			public Sig makeSig() throws Err {
				return new Sig.PrimSig("intref/IntRef" + id++);
			}
			@Override
			public void addFactor(Sig factor) { }
		};
    }

    private void parseModule(String doc) throws Err {
        Map<String,String> fm = new HashMap<String, String>();
        fm.put("/tmp/x", doc);
        fm.put("/tmp/util/intref.als", intrefmod);
        module = CompUtil.parseEverything_fromFile(null, fm, "/tmp/x");
    }

    private static void assertStdSigsAreTheSame(CompModule module, IntRefPreprocessor p) {
        Map<String, Sig> modsigs = new HashMap<String, Sig>();
        Map<String, Sig> presigs = new HashMap<String, Sig>();
        for (Sig s: module.getAllReachableSigs()) { modsigs.put(s.toString(), s); }
        for (Sig s: p.sigs) { presigs.put(s.toString(), s); }
        for (String name: stdsigs) {
            assertEquals(modsigs.get(name), presigs.get(name));
        }
    }

    @Test
    public void retainNormalSigs() throws Err {
        parseModule(simpleModuleDoc);
        IntRefPreprocessor p = IntRefPreprocessor.processModule(module);
        ConstList<Sig> msigs = module.getAllReachableSigs();
        ConstList<Sig> nsigs = p.sigs;

        assertEquals(msigs, nsigs);
        assertStdSigsAreTheSame(module, p);
        assertTrue("There should be no new instance for sig X.", 
        		p.sigs.contains(Helpers.getSigByName(module.getAllReachableSigs(), "this/X")));
    }

    @Test
    public void retainNormalSigs2() throws Err {
        parseModule("open util/intref\n" + simpleModuleDoc);
        IntRefPreprocessor p = IntRefPreprocessor.processModule(module);
        ConstList<Sig> msigs = module.getAllReachableSigs();
        ConstList<Sig> nsigs = p.sigs;

        assertEquals(msigs, nsigs);
        assertStdSigsAreTheSame(module, p);
        assertTrue("There should be no new instance for sig X.", 
        		p.sigs.contains(Helpers.getSigByName(module.getAllReachableSigs(), "this/X")));
    }

    private void assertDeclConversion(String decl, String newDecl) throws Err {
        String modstr = "open util/intref\nsig A {}\nsig X { v: " + decl + " }\n";
		parseModule(modstr);
		Sig sig = Helpers.getSigByName(module.getAllReachableSigs(), "this/X");
		Sig.Field field = Helpers.getFieldByName(sig.getFields(), "v");
		assertNotNull(field);
		Expr exprN = IntRefPreprocessor.convertExpr(field.decl().expr, sigbuilder);
		assertNotNull(exprN);
        assertEquals(decl, field.decl().expr.toString());
        assertEquals(newDecl, exprN.toString());
    }

    @Test
    public void convertFieldDecl() throws Err {
        assertDeclConversion("one this/A",        "one this/A");
        assertDeclConversion("one Int",           "one intref/IntRef1");
        assertDeclConversion("univ -> Int",       "univ -> intref/IntRef2");
        assertDeclConversion("Int -> Int",        "intref/IntRef3 -> intref/IntRef4");
        assertDeclConversion("this/A -> Int",     "this/A -> intref/IntRef5");
        assertDeclConversion("this/A ->lone Int", "this/A ->lone intref/IntRef6");
    }
    
    private void preprocessModule(String doc) throws Err {
    	parseModule(doc);
    	ppresult = IntRefPreprocessor.processModule(module);
    	assertStdSigsAreTheSame(module, ppresult);
    }
    
    private void assertConvFieldDecl(String sigName, String fieldName, String expDecl) {
    	Sig sig = Helpers.getSigByName(ppresult.sigs, sigName);
    	Sig.Field field = Helpers.getFieldByName(sig.getFields(), fieldName);
    	assertNotNull("Field " + fieldName + " not found!", field);
    	assertEquals(expDecl, field.decl().expr.toString());
    }
    
    private void assertSigExists(String sigName) {
    	assertNotNull("Sig " + sigName + " does not exist", Helpers.getSigByName(ppresult.sigs, sigName));
    }

    @Test
    public void convertIntSigs() throws Err {
        preprocessModule(
        		"open util/intref\n" +
        		"sig X { v: Int }\n" +
        		"sig Y { w: X ->one Int, u: Y ->one Int ->one Int }");
        assertFalse("A new instance for sig X should have been created",
        		ppresult.sigs.contains(Helpers.getSigByName(module.getAllReachableSigs(), "this/X")));
        assertNotNull(ppresult.intref);
        assertConvFieldDecl("this/X", "v", "one this/X$v$IntRef0");
        assertConvFieldDecl("this/Y", "w", "this/X ->one this/Y$w$IntRef0");
        assertConvFieldDecl("this/Y", "u", "this/Y ->one this/Y$u$IntRef0 ->one this/Y$u$IntRef1");
        assertSigExists("this/Y$w$IntRef0");
        assertSigExists("intref/IntRef");
        Sig.PrimSig sig = (PrimSig) Helpers.getSigByName(ppresult.sigs, "this/Y$w$IntRef0");
        assertEquals("intref/IntRef", sig.parent.label);
        assertEquals(ppresult.intref, sig.parent);
    }
    
    @Test
    public void intRefBounds() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"sig X { v: Int }\n" +
    			"pred show {}\n" +
    			"run show for 4 X\n" +
    			"run show for exactly 4 X\n");
    	assertEquals("Run show for 4 X", module.getAllCommands().get(0).toString());
    	assertEquals("Run show for 4 X, 4 X$v$IntRef0", ppresult.commands.get(0).toString());
    	assertEquals("Run show for exactly 4 X", module.getAllCommands().get(1).toString());
    	assertEquals("Run show for exactly 4 X, 4 X$v$IntRef0", ppresult.commands.get(1).toString());
    }
    
    @Test
    public void intRefBounds2() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"sig X { v: Y ->one Int, w: X -> Y ->one Int }\n" +
    			"sig Y {}\n" +
    			"pred show {}\n" +
    			"run show for 4 X, 3 Y\n");
    	assertEquals("Run show for 4 X, 3 Y", module.getAllCommands().get(0).toString());
    	assertEquals("Run show for 4 X, 3 Y, 12 X$v$IntRef0, 48 X$w$IntRef0",
    			ppresult.commands.get(0).toString());
    }
    
    @Test
    public void intRefBounds3() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"sig X { v: Int ->one Int }\n" +
    			"pred show {}\n" +
    			"run show for 5 X\n");
    	assertEquals("Run show for 5 X", module.getAllCommands().get(0).toString());
    	assertEquals("Run show for 5 X, 5 X$v$IntRef0, 5 X$v$IntRef1",
    			ppresult.commands.get(0).toString());
    }
    
    @Test
    public void intRefBounds4() throws Err {
    	preprocessModule(    			
    			"open util/intref\n" +
    			"sig X { v: Y ->one Int -> Y }\n" +
    			"sig Y {}\n" +
    			"pred show {}\n" +
    			"run show for 5 X, 6 Y\n");
    	assertEquals("Run show for 5 X, 6 Y", module.getAllCommands().get(0).toString());
    	assertEquals("Run show for 5 X, 6 Y, 180 X$v$IntRef0", ppresult.commands.get(0).toString());
    }
    
    @Test
    public void oneSigBounds() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"one sig X { u: Int, v: Y ->one Int, w: Z ->one Int }\n" +
    			"sig Y {}\n" +
    			"one sig Z {}\n" +
    			"pred show {}\n" +
    			"run show for 4 Y\n");
    	assertEquals("Run show for 4 Y", module.getAllCommands().get(0).toString());
    	assertEquals("Run show for 4 Y, 1 X$u$IntRef0, 4 X$v$IntRef0, 1 X$w$IntRef0",
    			ppresult.commands.get(0).toString());
    	
    	Sig sigXold = Helpers.getSigByName(module.getAllReachableSigs(), "this/X");
    	Sig sigXnew = Helpers.getSigByName(ppresult.sigs, "this/X");
    	Sig sigYold = Helpers.getSigByName(module.getAllReachableSigs(), "this/Y");
    	Sig sigYnew = Helpers.getSigByName(ppresult.sigs, "this/Y");
    	assertNotNull(sigXold.isOne);
    	assertNotNull(sigXnew.isOne);
    	assertEquals(sigYold, sigYnew);
    	assertNull(sigYold.isOne);
    }
    
    @Test
    public void unchangedFacts() throws Err {
    	preprocessModule(
    		"open util/intref\n" +
    		"sig A {}\n" +
    		"sig B { m: A -> A}\n" +
    		"pred testeq[a: A, b: B] { let a2 = b.m[a] | a2 != a }\n" +
    		"fact { all b: B, a: A { let a2 = a | testeq[a2, b] } }\n" +
    		"fact { all b: B, a: A { b.m[a] = a implies b.m[a] = a else b.m[a] != a } }\n" +
    		"pred show {}\n" +
    		"run show for 4");
    	assertEquals(module.getAllReachableFacts().toString(), ppresult.facts.toString());
    }
    
    @Test
    public void factExpr() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"one sig A { v: Int }\n" +
    			"fact { A.v + 2 = 4 }\n" +
    			"pred show {}\n" +
    			"run show for 3\n");
    	assertEquals("AND[int[this/A . (this/A <: v)] + 2 = 4]", module.getAllReachableFacts().toString());
    	assertEquals("AND[intexpr_0 . (intref/IntRef <: aqclass) = this/A . (this/A <: v) . (intref/IntRef <: aqclass)]", 
    			ppresult.facts.toString());
    	assertEquals(1, ppresult.hysatExprs.size());
    	assertEquals("((intexpr_0 + 2) = 4)", ppresult.hysatExprs.get(0));
    }
}
