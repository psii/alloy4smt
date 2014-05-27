package de.psi.alloy4smt.ast;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import org.junit.Before;
import org.junit.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import static org.junit.Assert.*;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

public class SmtPreprocessorTest {

    public static final String docPrelude = "open util/smtint\n";

    private CompModule module;
    private List<PreparedCommand> commands;

    @Before
    public void setUp() {
        module = null;
        commands = null;
    }

    private void parseModule(String doc) throws Err {
        Map<String,String> fm = new HashMap<String, String>();
        fm.put("/tmp/x", docPrelude + doc);
        module = CompUtil.parseEverything_fromFile(null, fm, "/tmp/x");
        assertTrue(module.getAllCommands().size() > 0);
        commands = new Vector<PreparedCommand>();
        for (Command c : module.getAllCommands()) {
            commands.add(SmtPreprocessor.build(c, module.getAllReachableSigs()));
        }
    }

    private Sig getOldSig(String name) {
        return Helpers.getSigByName(module.getAllReachableSigs(), name);
    }

    private Sig.Field getOldField(String signame, String field) {
        Sig sig = getOldSig(signame);
        return Helpers.getFieldByName(sig.getFields(), field);
    }

    private Sig getNewSig(String name) {
        return Helpers.getSigByName(commands.get(0).sigs, name);
    }

    private Sig.Field getNewField(String signame, String field) {
        Sig sig = getNewSig(signame);
        return Helpers.getFieldByName(sig.getFields(), field);
    }

    private void assertFields(String signame, String fieldname, String oldrepr, String newrepr) {
        Sig.Field oldf = getOldField(signame, fieldname);
        Sig.Field newf = getNewField(signame, fieldname);
        assertEquals(oldrepr, oldf.decl().expr.toString());
        assertEquals(newrepr, newf.decl().expr.toString());
    }

    @Test
    public void simpleTest() throws Err {
        parseModule(
                "sig X { v: Y }\n" +
                "sig Y { w: X ->one X }\n" +
                "pred show {}\n" +
                "run show for 2 X, 2 Y\n");
        assertFields("this/X", "v", "one this/Y", "one this/Y");
        assertFields("this/Y", "w", "this/X ->one this/X", "this/X ->one this/X");
    }

    private void assertDeclConversion(String decl, String newDecl) throws Err {
        parseModule("sig A {}\nsig X { v: " + decl + " }\npred show{}\nrun show for 2 A, 2 X\n");
        assertFields("this/X", "v", decl, newDecl);
    }

    @Test
    public void oneIntegerTest() throws Err {
        assertDeclConversion("one this/A",        "one this/A");
        assertDeclConversion("one smtint/Sint", "one this/X_v_SintRef");
        assertDeclConversion("univ ->one smtint/Sint",    "univ ->one this/X_v_SintRef");
        assertDeclConversion("this/A ->one smtint/Sint",  "this/A ->one this/X_v_SintRef");
        assertDeclConversion("this/A ->lone smtint/Sint", "this/A ->lone this/X_v_SintRef");
    }

    @Test
    public void intRefBounds() throws Err {
        parseModule(
                "sig X { v: Sint }\n" +
                "pred show{}\n" +
                "run show for 4 X\n");
        assertEquals("Run show for 4 X", module.getAllCommands().get(0).toString());
        assertEquals("Run show for exactly 4 X_v_SintRef, 4 X",
                commands.get(0).command.toString());
    }

    @Test
    public void intRefBounds2() throws Err {
        parseModule(
                "sig X { v: Y ->one Sint, w: X -> Y ->one Sint }\n" +
                        "sig Y {}\n" +
                        "pred show {}\n" +
                        "run show for 4 X, 3 Y\n"
        );
        assertEquals("Run show for 4 X, 3 Y", module.getAllCommands().get(0).toString());
        assertEquals("Run show for exactly 12 X_v_SintRef, exactly 48 X_w_SintRef, 4 X, 3 Y",
                commands.get(0).command.toString());
    }

    @Test
    public void intRefBounds3() throws Err {
        parseModule(
                "sig X { v: Y ->one Sint -> Y }\n" +
                        "sig Y {}\n" +
                        "pred show {}\n" +
                        "run show for 5 X, 6 Y\n"
        );
        assertEquals("Run show for 5 X, 6 Y", module.getAllCommands().get(0).toString());
        assertEquals("Run show for exactly 180 X_v_SintRef, 5 X, 6 Y",
                commands.get(0).command.toString());
    }

    @Test
    public void oneSigBounds() throws Err {
        parseModule(
                        "one sig X { u: Sint, v: Y ->one Sint, w: Z ->one Sint }\n" +
                        "sig Y {}\n" +
                        "one sig Z {}\n" +
                        "pred show {}\n" +
                        "run show for 4 Y\n");
        assertEquals("Run show for 4 Y", module.getAllCommands().get(0).toString());
        assertEquals("Run show for 4 Y, exactly 1 X_u_SintRef, exactly 4 X_v_SintRef, exactly 1 X_w_SintRef",
                commands.get(0).command.toString());

        Sig sigXold = Helpers.getSigByName(module.getAllReachableSigs(), "this/X");
        Sig sigXnew = Helpers.getSigByName(commands.get(0).sigs, "this/X");
        Sig sigYold = Helpers.getSigByName(module.getAllReachableSigs(), "this/Y");
        Sig sigYnew = Helpers.getSigByName(commands.get(0).sigs, "this/Y");
        assertNotNull(sigXold.isOne);
        assertNotNull(sigXnew.isOne);
        assertNull(sigYold.isOne);
        assertNull(sigYnew.isOne);
    }

    @Test
    public void implicitSigBounds() throws Err {
        parseModule(
                        "sig X { v: Y ->one Sint }\n" +
                        "sig Y {}\n" +
                        "one sig Z { u: Y ->one Sint }\n" +
                        "pred show {}\n" +
                        "run show for 3 but 4 Y\n" +
                        "run show for 3\n");
        assertEquals("Run show for 3 but 4 Y", module.getAllCommands().get(0).toString());
        assertEquals("Run show for 3 but 4 Y, exactly 12 X_v_SintRef, exactly 4 Z_u_SintRef",
                commands.get(0).command.toString());
        assertEquals("Run show for 3", module.getAllCommands().get(1).toString());
        assertEquals("Run show for 3 but exactly 9 X_v_SintRef, exactly 3 Z_u_SintRef",
                commands.get(1).command.toString());
    }

    @Test
    public void unchangedFacts() throws Err {
        parseModule(
                        "sig A {}\n" +
                        "sig B { m: A -> A}\n" +
                        "pred testeq[a: A, b: B] { let a2 = b.m[a] | a2 != a }\n" +
                        "fact { all b: B, a: A { let a2 = a | testeq[a2, b] } }\n" +
                        "fact { all b: B, a: A { b.m[a] = a implies b.m[a] = a else b.m[a] != a } }\n" +
                        "pred show {}\n" +
                        "run show for 4");
        assertEquals(module.getAllReachableFacts().toString(), commands.get(0).command.formula.toString());
    }

    @Test
    public void rewriteFactsAndExtractIntExprs() throws Err {
        parseModule(
                        "one sig A { v: Sint }\n" +
                        "fact { A.v.plus[const[2]] = const[4] }\n" +
                        "fact { A.v.gt[const[0]] }\n" +
                        "pred show {}\n" +
                        "run show for 3\n");
        assertEquals(
                "AND[" +
                        "smtint/plus[this/A . (this/A <: v), smtint/const[Int[2]]] = smtint/const[Int[4]], " +
                        "smtint/gt[this/A . (this/A <: v), smtint/const[Int[0]]]" +
                        "]",
                module.getAllReachableFacts().toString());
        assertEquals("[smtint/SintRef, univ, Int, seq/Int, String, none, this/A, this/A_v_SintRef, smtint/Sint, " +
                "SintExpr0, SintExpr1, SintExpr2, SintExpr3]", commands.get(0).sigs.toString());

        assertEquals("[(= SintExpr1$0 (+ SintExpr0$0 2)), (= SintExpr2$0 4), (> SintExpr3$0 0)]",
                commands.get(0).smtExprs.toString());
        assertEquals(
                "AND[" +
                        "SintExpr0 . (smtint/SintRef <: aqclass) = this/A . (this/A <: v) . (smtint/SintRef <: aqclass), " +
                        "SintExpr3 . (smtint/SintRef <: aqclass) = this/A . (this/A <: v) . (smtint/SintRef <: aqclass), " +
                        "SintExpr1 . (smtint/SintRef <: aqclass) = SintExpr2 . (smtint/SintRef <: aqclass)" +
                "]",
                commands.get(0).command.formula.toString());

        assertEquals("Run show for 3 but exactly 1 A_v_SintRef, exactly 1 SintExpr0, exactly 1 SintExpr1, exactly 1 SintExpr2, exactly 1 SintExpr3",
                commands.get(0).command.toString());
    }

    @Test
    public void rewriteFactsAndExtractIntExprsInQuantifiedFormula() throws Err {
        parseModule(
                        "sig A { v: Sint }\n" +
                        "fact { all a: A | a.v.plus[const[2]].eq[const[4]] }\n" +
                        "pred show {}\n" +
                        "run show for 3 A\n");
        assertEquals("AND[(all a | smtint/eq[smtint/plus[a . (this/A <: v), smtint/const[Int[2]]], smtint/const[Int[4]]])]",
                module.getAllReachableFacts().toString());
        assertEquals("AND[" +
                "(all a | (SintExpr0 <: map) . a . (smtint/SintRef <: aqclass) = " +
                "a . (this/A <: v) . (smtint/SintRef <: aqclass))" +
                "]", commands.get(0).command.formula.toString());
        assertEquals("Run show for 3 A, exactly 3 A_v_SintRef, exactly 3 SintExpr0",
                commands.get(0).command.toString());
/*
        assertIntexprBound(0, "[" +
                "[IntExpr0$0, A$0], " +
                "[IntExpr0$1, A$1], " +
                "[IntExpr0$2, A$2]" +
                "]");

        List<String> expectedHysatExprs = new Vector<String>();
        expectedHysatExprs.add("((IntExpr0$0 + 2) = 4)");
        expectedHysatExprs.add("((IntExpr0$1 + 2) = 4)");
        expectedHysatExprs.add("((IntExpr0$2 + 2) = 4)");
        assertEquals(expectedHysatExprs, ppresult.commands.get(0).hysatExprs);
*/

    }
}
