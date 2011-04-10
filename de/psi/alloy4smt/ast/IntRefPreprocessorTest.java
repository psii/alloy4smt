package de.psi.alloy4smt.ast;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import kodkod.instance.Universe;

import org.junit.Before;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitQuery;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;


public class IntRefPreprocessorTest {

    private static final String simpleModuleDoc =
            "sig X { v: Y }\n" +
            "sig Y { w: X ->one X }\n";

    private static final String intrefmod =
            "module util/intref\n" +
            "abstract sig IntRef { aqclass: IntRef }\n";

    private static final String[] stdsigs = { "univ", "Int", "seq/Int", "String", "none" };

    private CompModule module;
    private IntRefPreprocessor ppresult;

    @Before
    public void setUp() {
        module = null;
        ppresult = null;
    }

    private void parseModule(String doc) throws Err {
        Map<String,String> fm = new HashMap<String, String>();
        fm.put("/tmp/x", doc);
        fm.put("/tmp/util/intref.als", intrefmod);
        module = CompUtil.parseEverything_fromFile(null, fm, "/tmp/x");
    }

    private void preprocessModule(String doc) throws Err {
    	parseModule(doc);
    	ppresult = IntRefPreprocessor.processModule(module);
    	assertStdSigsAreTheSame(module, ppresult);
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
    public void retainSigsIfUtilIntrefIsNotUsed() throws Err {
        preprocessModule(simpleModuleDoc);
        ConstList<Sig> msigs = module.getAllReachableSigs();
        ConstList<Sig> nsigs = ppresult.sigs;

        assertEquals(msigs, nsigs);
        assertTrue("There should be no new instance for sig X.", 
        		ppresult.sigs.contains(Helpers.getSigByName(module.getAllReachableSigs(), "this/X")));
    }

    private void assertDeclConversion(String decl, String newDecl) throws Err {
        String modstr = "open util/intref\nsig A {}\nsig X { v: " + decl + " }\n";
		preprocessModule(modstr);
		Sig sig = Helpers.getSigByName(module.getAllReachableSigs(), "this/X");
		Sig.Field field = Helpers.getFieldByName(sig.getFields(), "v");
		assertNotNull(field);
		Sig newsig = Helpers.getSigByName(ppresult.sigs, "this/X");
		Sig.Field newfield = Helpers.getFieldByName(newsig.getFields(), "v");
		assertNotNull(newfield);
        assertEquals(decl, field.decl().expr.toString());
        assertEquals(newDecl, newfield.decl().expr.toString());
    }

    @Test
    public void convertFieldDecl() throws Err {
        assertDeclConversion("one this/A",        "one this/A");
        assertDeclConversion("one Int",           "one this/X_v_IntRef");
        assertDeclConversion("univ ->one Int",    "univ ->one this/X_v_IntRef");
        assertDeclConversion("this/A ->one Int",  "this/A ->one this/X_v_IntRef");
        assertDeclConversion("this/A ->lone Int", "this/A ->lone this/X_v_IntRef");
    }
    
    private void assertInvalidDecls(String decl) throws Err {
    	String modstr = "open util/intref\nsig A {}\nsig X { v: " + decl + " }\n";
    	try {
    		preprocessModule(modstr);
    		fail();
    	} catch (ErrorFatal e) {
    		assertTrue(e.msg.contains("unsupported decl"));
    	}
    }
    
    @Test
    public void invalidFieldDecl() throws Err {
    	//assertInvalidDecls("this/A -> Int");
    	assertInvalidDecls("Int -> Int");
    	//assertInvalidDecls("univ -> Int");
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
        		"sig Y { w: X ->one Int, u: Y ->one Int }");
        assertFalse("A new instance for sig X should have been created",
        		ppresult.sigs.contains(Helpers.getSigByName(module.getAllReachableSigs(), "this/X")));
        assertNotNull(ppresult.intref);
        assertConvFieldDecl("this/X", "v", "one this/X_v_IntRef");
        assertConvFieldDecl("this/Y", "w", "this/X ->one this/Y_w_IntRef");
        assertConvFieldDecl("this/Y", "u", "this/Y ->one this/Y_u_IntRef");
        assertSigExists("this/Y_w_IntRef");
        assertSigExists("intref/IntRef");
        Sig.PrimSig sig = (PrimSig) Helpers.getSigByName(ppresult.sigs, "this/Y_w_IntRef");
        Sig.PrimSig intref = (PrimSig) Helpers.getSigByName(ppresult.sigs, "intref/IntRef");
        assertEquals(intref, ppresult.intref);
        assertEquals("intref/IntRef", sig.parent.label);
        assertEquals(ppresult.intref, sig.parent);
        assertEquals(3, ppresult.intref.children().size());
        assertTrue(ppresult.intref.children().contains(sig));
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
    	assertEquals("Run show for 4 X, exactly 4 X_v_IntRef", ppresult.commands.get(0).command.toString());
    	assertEquals("Run show for exactly 4 X", module.getAllCommands().get(1).toString());
    	assertEquals("Run show for exactly 4 X, exactly 4 X_v_IntRef", ppresult.commands.get(1).command.toString());
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
    	assertEquals("Run show for 4 X, 3 Y, exactly 12 X_v_IntRef, exactly 48 X_w_IntRef",
    			ppresult.commands.get(0).command.toString());
    }
    
    @Test
    public void intRefBounds3() throws Err {
    	preprocessModule(    			
    			"open util/intref\n" +
    			"sig X { v: Y ->one Int -> Y }\n" +
    			"sig Y {}\n" +
    			"pred show {}\n" +
    			"run show for 5 X, 6 Y\n");
    	assertEquals("Run show for 5 X, 6 Y", module.getAllCommands().get(0).toString());
    	assertEquals("Run show for 5 X, 6 Y, exactly 180 X_v_IntRef", ppresult.commands.get(0).command.toString());
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
    	assertEquals("Run show for 4 Y, exactly 1 X_u_IntRef, exactly 4 X_v_IntRef, exactly 1 X_w_IntRef",
    			ppresult.commands.get(0).command.toString());
    	
    	Sig sigXold = Helpers.getSigByName(module.getAllReachableSigs(), "this/X");
    	Sig sigXnew = Helpers.getSigByName(ppresult.sigs, "this/X");
    	Sig sigYold = Helpers.getSigByName(module.getAllReachableSigs(), "this/Y");
    	Sig sigYnew = Helpers.getSigByName(ppresult.sigs, "this/Y");
    	assertNotNull(sigXold.isOne);
    	assertNotNull(sigXnew.isOne);
    	assertNull(sigYold.isOne);
    	assertNull(sigYnew.isOne);
    }
    
    @Test
    public void implicitSigBounds() throws Err {
    	preprocessModule(    			
    			"open util/intref\n" +
    			"sig X { v: Y ->one Int }\n" +
    			"sig Y {}\n" +
    			"one sig Z { u: Y ->one Int }\n" +
    			"pred show {}\n" +
    			"run show for 3 but 4 Y\n" +
    			"run show for 3\n");
    	assertEquals("Run show for 3 but 4 Y", module.getAllCommands().get(0).toString());
    	assertEquals("Run show for 3 but 4 Y, exactly 12 X_v_IntRef, exactly 4 Z_u_IntRef", 
    			ppresult.commands.get(0).command.toString());
    	assertEquals("Run show for 3", module.getAllCommands().get(1).toString());
    	assertEquals("Run show for 3 but exactly 9 X_v_IntRef, exactly 3 Z_u_IntRef", 
    			ppresult.commands.get(1).command.toString());
    }
    
    private static class FindAllSigs extends VisitQuery<Object> {
    	
    	public final List<Sig> sigs = new Vector<Sig>();

		@Override
		public Object visit(Sig x) throws Err {
			sigs.add(x);
			return super.visit(x);
		}
    	
    }
    
    @Test
    public void oldSigsAreNotReferencedAnymore() throws Err {
    	preprocessModule(    			
    			"open util/intref\n" +
    			"sig X { v: Y ->one Int, r: Y } { all y: Y | r = y }\n" +
    			"sig Y { f: X } { all x: X | f = x }\n" +
    			"one sig Z { u: Y ->one Int }\n" +
    			"fact { all x: X, y: Y | x.r = y }\n" +
    			"pred show {}\n" +
    			"run show for 3 but 4 Y\n");
    	
    	FindAllSigs fas = new FindAllSigs();
    	fas.visitThis(ppresult.commands.get(0).command.formula);
    	for (Sig sig : ppresult.sigs) {
    		for (Expr expr : sig.getFacts()) fas.visitThis(expr);
    		for (Field field : sig.getFields()) fas.visitThis(field.decl().expr);
    	}
    	assertTrue("fas.sigs = " + fas.sigs.size(), fas.sigs.size() >= 3);
    	for (Sig sig : fas.sigs) {
    		assertTrue("Old sig remains: " + sig.label, ppresult.sigs.contains(sig));
    	}
    }
    
    @Test
    public void sigFactsAreRetained() throws Err {
    	preprocessModule(    			
    			"open util/intref\n" +
    			"sig X { v: Y ->one Int, r: Y } { all y: Y | r = y }\n" +
    			"sig Y { f: X } { all x: X | f = x }\n" +
    			"one sig Z { u: Y ->one Int }\n" +
    			"pred show {}\n" +
    			"run show for 3 but 4 Y\n");
    	
    	assertTrue(Helpers.getSigByName(ppresult.sigs, "this/X").getFacts().size() > 0);
    	assertTrue(Helpers.getSigByName(ppresult.sigs, "this/Y").getFacts().size() > 0);
    	assertTrue(Helpers.getSigByName(ppresult.sigs, "this/Z").getFacts().size() == 0);
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
    	assertEquals(module.getAllReachableFacts().toString(), ppresult.commands.get(0).command.formula.toString());
    }
    
    @Test
    public void rewriteFactsAndExtractIntExprs() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"one sig A { v: Int }\n" +
    			"fact { A.v + 2 = 4 }\n" +
    			"fact { A.v > 0 }\n" +
    			"pred show {}\n" +
    			"run show for 3\n");
    	assertEquals("AND[int[this/A . (this/A <: v)] + 2 = 4, int[this/A . (this/A <: v)] > 0]",
    			module.getAllReachableFacts().toString());
    	assertEquals(
    			"AND[" +
    			"IntExpr0 . (intref/IntRef <: aqclass) = this/A . (this/A <: v) . (intref/IntRef <: aqclass), " +
    			"IntExpr1 . (intref/IntRef <: aqclass) = this/A . (this/A <: v) . (intref/IntRef <: aqclass)" +
    			"]", 
    			ppresult.commands.get(0).command.formula.toString());
    	assertEquals(2, ppresult.commands.get(0).hysatExprs.size());
    	assertEquals("((IntExpr0 + 2) = 4)", ppresult.commands.get(0).hysatExprs.get(0));
    	assertEquals("(IntExpr1 > 0)", ppresult.commands.get(0).hysatExprs.get(1));
    	assertNotNull(Helpers.getSigByName(ppresult.commands.get(0).sigs, "IntExpr0"));
    	assertNotNull(Helpers.getSigByName(ppresult.commands.get(0).sigs, "IntExpr1"));
    }
    
    @Test
    public void rewriteFactsWithIntExprsAndNormalExprs() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"one sig A { v: Int }\n" +
    			"one sig Y { y: Y }\n" +
    			"fact { A.v + 2 = 4 }\n" +
    			"fact { Y.y = Y }\n" +
    			"pred show {}\n" +
    			"run show for 3\n");
    	assertEquals("AND[int[this/A . (this/A <: v)] + 2 = 4, this/Y . (this/Y <: y) = this/Y]",
    			module.getAllReachableFacts().toString());    	
    	assertEquals(
    			"AND[" +
    			"IntExpr0 . (intref/IntRef <: aqclass) = this/A . (this/A <: v) . (intref/IntRef <: aqclass), " +
    			"this/Y . (this/Y <: y) = this/Y" +
    			"]", 
    			ppresult.commands.get(0).command.formula.toString());
    	assertEquals(1, ppresult.commands.get(0).hysatExprs.size());
    	assertEquals("((IntExpr0 + 2) = 4)", ppresult.commands.get(0).hysatExprs.get(0));
    }
    
    @Test
    public void rewriteFactsWithIntsOnLeftAndRightSide() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"one sig A { v: Int }\n" +
    			"one sig B { u: Int }\n" +
    			"one sig C { m: Int }\n" +
    			"one sig D { n: Int }\n" +
    			"fact { int(A.v) + int(B.u) = 4 }\n" +
    			"fact { C.m + D.n = 4 }\n" +
    			"pred show {}\n" +
    			"run show for 3\n");
    	assertEquals("AND[" +
    			"int[this/A . (this/A <: v)] + int[this/B . (this/B <: u)] = 4, " +
    			"int[this/C . (this/C <: m) + this/D . (this/D <: n)] = 4" +
    			"]", 
    			module.getAllReachableFacts().toString());
    	assertEquals("AND[" +
    			"IntExpr0 . (intref/IntRef <: aqclass) = this/A . (this/A <: v) . (intref/IntRef <: aqclass), " +
    			"IntExpr1 . (intref/IntRef <: aqclass) = this/B . (this/B <: u) . (intref/IntRef <: aqclass), " +
    			"IntExpr2 . (intref/IntRef <: aqclass) = this/C . (this/C <: m) . (intref/IntRef <: aqclass), " +
    			"IntExpr3 . (intref/IntRef <: aqclass) = this/D . (this/D <: n) . (intref/IntRef <: aqclass)" +
    			"]",
    			ppresult.commands.get(0).command.formula.toString());
    }
    
    @Test
    public void rewriteFactsAndExtractIntExprsInQuantifiedFormula() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"sig A { v: Int }\n" +
    			"fact { all a: A | a.v + 2 = 4 }\n" +
    			"pred show {}\n" +
    			"run show for 3\n");
    	assertEquals("AND[(all a | int[a . (this/A <: v)] + 2 = 4)]", module.getAllReachableFacts().toString());
    	// TODO: actual test
    }
    
    private void assertIntRefEqualsTupleSet(String tuplesetstr) {
    	final Universe universe = new Universe(ppresult.commands.get(0).intrefAtoms);
    	assertEquals(tuplesetstr, ppresult.commands.get(0).getIntRefEqualsTupleSet(universe.factory()).toString());
    }
    
    @Test
    public void collectIntRefAtoms() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"one sig A { v: Int, w: B ->one Int }\n" +
    			"sig B {}\n" +
    			"pred show {}\n" +
    			"run show for 3\n");
    	assertEquals("Run show for 3 but exactly 1 A_v_IntRef, exactly 3 A_w_IntRef", 
    			ppresult.commands.get(0).command.toString());
    	
    	List<String> intrefatoms = new Vector<String>();
    	intrefatoms.add("A_v_IntRef_0");
    	intrefatoms.add("A_w_IntRef_0");
    	intrefatoms.add("A_w_IntRef_1");
    	intrefatoms.add("A_w_IntRef_2");
    	assertEquals(intrefatoms, ppresult.commands.get(0).intrefAtoms);
    	
    	assertIntRefEqualsTupleSet("[" +
    			"[A_v_IntRef_0, A_w_IntRef_0], " +
    			"[A_v_IntRef_0, A_w_IntRef_1], " +
    			"[A_v_IntRef_0, A_w_IntRef_2], " +
    			"[A_w_IntRef_0, A_w_IntRef_1], " +
    			"[A_w_IntRef_0, A_w_IntRef_2], " +
    			"[A_w_IntRef_1, A_w_IntRef_2]" +
    			"]");
    }

    @Test
    public void collectIntRefAtomsFromFacts() throws Err {
    	preprocessModule(
    			"open util/intref\n" +
    			"one sig A { v: Int, w: B ->one Int }\n" +
    			"sig B {}\n" +
    			"fact { A.v + 2 = 4 }\n" +
    			"fact { A.v > 0 }\n" +
    			"pred show {}\n" +
    			"run show for 3\n");
    	assertEquals("Run show for 3 but exactly 1 A_v_IntRef, exactly 3 A_w_IntRef", 
    			ppresult.commands.get(0).command.toString());
    	
    	List<String> intrefatoms = new Vector<String>();
    	intrefatoms.add("A_v_IntRef_0");
    	intrefatoms.add("A_w_IntRef_0");
    	intrefatoms.add("A_w_IntRef_1");
    	intrefatoms.add("A_w_IntRef_2");
    	intrefatoms.add("IntExpr0_0");
    	intrefatoms.add("IntExpr1_0");
    	assertEquals(intrefatoms, ppresult.commands.get(0).intrefAtoms);
    	
    	assertIntRefEqualsTupleSet("[" +
    			"[A_v_IntRef_0, A_w_IntRef_0], " +
    			"[A_v_IntRef_0, A_w_IntRef_1], " +
    			"[A_v_IntRef_0, A_w_IntRef_2], " +
    			"[A_v_IntRef_0, IntExpr0_0], " +
    			"[A_v_IntRef_0, IntExpr1_0], " +
    			"[A_w_IntRef_0, A_w_IntRef_1], " +
    			"[A_w_IntRef_0, A_w_IntRef_2], " +
    			"[A_w_IntRef_0, IntExpr0_0], " +
    			"[A_w_IntRef_0, IntExpr1_0], " +
    			"[A_w_IntRef_1, A_w_IntRef_2], " +
    			"[A_w_IntRef_1, IntExpr0_0], " +
    			"[A_w_IntRef_1, IntExpr1_0], " +
    			"[A_w_IntRef_2, IntExpr0_0], " +
    			"[A_w_IntRef_2, IntExpr1_0], " +
    			"[IntExpr0_0, IntExpr1_0]" +
    			"]");
    }
}
