package de.psi.alloy4smt.ast;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.BoundsComputer;
import edu.mit.csail.sdg.alloy4compiler.translator.ScopeComputer;
import kodkod.ast.Relation;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
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
    public static final String smtintFacts =
            "(all a,b | AND[" +
              "OR[" +
                "b in a . (smtint/SintRef <: equals), " +
                "a in b . (smtint/SintRef <: equals)" +
              "] <=> a . (smtint/SintRef <: aqclass) = b . (smtint/SintRef <: aqclass), " +
              "b in a . (smtint/SintRef <: equals) => OR[" +
                "b . (smtint/SintRef <: aqclass) = a, " +
                "b . (smtint/SintRef <: aqclass) in a . (smtint/SintRef <: equals)" +
              "]" +
            "])";

    private CompModule module;
    private List<SmtPreprocessor.Result> commands;

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
        commands = new Vector<SmtPreprocessor.Result>();
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
        Sig.Field newf = getNewField(signame + "_c", fieldname + "_c");
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
        assertFields("this/X", "v", "one this/Y", "one this/Y_c");
        assertFields("this/Y", "w", "this/X ->one this/X", "this/X_c ->one this/X_c");
    }

    private void assertDeclConversion(String decl, String newDecl) throws Err {
        parseModule("sig A {}\nsig X { v: " + decl + " }\npred show{}\nrun show for 2 A, 2 X\n");
        assertFields("this/X", "v", decl, newDecl);
    }

    @Test
    public void oneIntegerTest() throws Err {
        assertDeclConversion("one this/A",        "one this/A_c");
        assertDeclConversion("one smtint/Sint", "one this/X_v_SintRef");
        assertDeclConversion("univ ->one smtint/Sint",    "univ ->one this/X_v_SintRef");
        assertDeclConversion("this/A ->one smtint/Sint",  "this/A_c ->one this/X_v_SintRef");
        assertDeclConversion("this/A ->lone smtint/Sint", "this/A_c ->lone this/X_v_SintRef");
    }

    @Test
    public void intRefBounds() throws Err {
        parseModule(
                "sig X { v: Sint }\n" +
                "pred show{}\n" +
                "run show for 4 X\n");
        assertEquals("Run show for 4 X", module.getAllCommands().get(0).toString());
        assertEquals("Run show for 4 X_c, exactly 4 X_v_SintRef",
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
        assertEquals("Run show for 4 X_c, 3 Y_c, exactly 12 X_v_SintRef, exactly 48 X_w_SintRef",
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
        assertEquals("Run show for 5 X_c, 6 Y_c, exactly 180 X_v_SintRef",
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
        assertEquals("Run show for 4 Y_c, exactly 1 X_u_SintRef, exactly 4 X_v_SintRef, exactly 1 X_w_SintRef",
                commands.get(0).command.toString());

        Sig sigXold = Helpers.getSigByName(module.getAllReachableSigs(), "this/X");
        Sig sigXnew = Helpers.getSigByName(commands.get(0).sigs, "this/X_c");
        Sig sigYold = Helpers.getSigByName(module.getAllReachableSigs(), "this/Y");
        Sig sigYnew = Helpers.getSigByName(commands.get(0).sigs, "this/Y_c");
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
        assertEquals("Run show for 3 but 4 Y_c, exactly 12 X_v_SintRef, exactly 4 Z_u_SintRef",
                commands.get(0).command.toString());
        assertEquals("Run show for 3", module.getAllCommands().get(1).toString());
        assertEquals("Run show for 3 but exactly 9 X_v_SintRef, exactly 3 Z_u_SintRef",
                commands.get(1).command.toString());
    }

/*
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
*/

    private static A4Options makeA4Options() {
        final A4Options opt = new A4Options();
        opt.recordKodkod = true;
        opt.tempDirectory = "/tmp";
        opt.solverDirectory = "/tmp";
        opt.solver = A4Options.SatSolver.SAT4J;
        opt.skolemDepth = 4;
        return opt;
    }

    private void assertEqualsTupleSet(String tuplesetstr) {
        final SmtPreprocessor.Result command = commands.get(0);
        final Relation rel = (Relation) command.solution.a2k(command.equalsf);
        final TupleSet lb = command.solution.getBounds().lowerBound(rel);
        final TupleSet ub = command.solution.getBounds().upperBound(rel);
        assertEquals(tuplesetstr, lb.toString());
        assertEquals(tuplesetstr, ub.toString());
    }

    private void assertSintexprBounds(int exprid, String tuplesetstr) {
        final SmtPreprocessor.Result command = commands.get(0);
        final Sig.PrimSig sintexpr = (Sig.PrimSig) Helpers.getSigByName(command.sigs, "SintExpr" + exprid);
        final Sig.Field sintmap = Helpers.getFieldByName(sintexpr.getFields(), "map");
        final Relation rel = (Relation) command.solution.a2k(sintmap);
        final TupleSet lb = command.solution.getBounds().lowerBound(rel);
        final TupleSet ub = command.solution.getBounds().upperBound(rel);
        assertEquals(tuplesetstr, lb.toString());
        assertEquals(tuplesetstr, ub.toString());
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
                        "smtint/gt[this/A . (this/A <: v), smtint/const[Int[0]]], " + smtintFacts +
                        "]",
                module.getAllReachableFacts().toString());


        assertEquals("[smtint/SintRef, univ, Int, seq/Int, String, none, this/A_c, this/A_v_SintRef, " +
                "SintExpr0, SintExpr1, SintExpr2, SintExpr3]", commands.get(0).sigs.toString());
        assertEquals("Run show for 3 but exactly 1 A_v_SintRef, exactly 1 SintExpr0, exactly 1 SintExpr1, exactly 1 SintExpr2, exactly 1 SintExpr3",
                commands.get(0).command.toString());
        assertEquals(
                "AND[" +
                        "SintExpr0 . (smtint/SintRef <: aqclass) = this/A_c . (this/A_c <: v_c) . (smtint/SintRef <: aqclass), " +
                        "SintExpr1 . (smtint/SintRef <: aqclass) = SintExpr2 . (smtint/SintRef <: aqclass), " +
                        "SintExpr3 . (smtint/SintRef <: aqclass) = this/A_c . (this/A_c <: v_c) . (smtint/SintRef <: aqclass), " +
                        smtintFacts +
                "]",
                commands.get(0).command.formula.toString());

        assertEqualsTupleSet("[" +
                "[A_v_SintRef$0, SintExpr0$0], " +
                "[A_v_SintRef$0, SintExpr1$0], " +
                "[A_v_SintRef$0, SintExpr2$0], " +
                "[A_v_SintRef$0, SintExpr3$0], " +
                "[SintExpr0$0, SintExpr1$0], " +
                "[SintExpr0$0, SintExpr2$0], " +
                "[SintExpr0$0, SintExpr3$0], " +
                "[SintExpr1$0, SintExpr2$0], " +
                "[SintExpr1$0, SintExpr3$0], " +
                "[SintExpr2$0, SintExpr3$0]" +
                "]");

        assertEquals("[(= SintExpr1$0 (+ SintExpr0$0 2)), (= SintExpr2$0 4), (> SintExpr3$0 0)]",
                commands.get(0).smtExprs.toString());

    }

    @Test
    public void rewriteFactsAndExtractIntExprsInQuantifiedFormula() throws Err {
        parseModule(
                        "sig A { v: Sint }\n" +
                        "fact { all a: A | a.v.plus[const[2]].eq[const[4]] }\n" +
                        "pred show {}\n" +
                        "run show for 3 A\n");
        assertEquals("AND[" +
                        "(all a | smtint/eq[smtint/plus[a . (this/A <: v), smtint/const[Int[2]]], smtint/const[Int[4]]]), " +
                        smtintFacts +
                        "]",
                module.getAllReachableFacts().toString());
        assertEquals("AND[" +
                "(all a | (SintExpr0 <: map) . a . (smtint/SintRef <: aqclass) = " +
                "a . (this/A_c <: v_c) . (smtint/SintRef <: aqclass)), " + smtintFacts +
                "]", commands.get(0).command.formula.toString());
        assertEquals("Run show for 3 A_c, exactly 3 A_v_SintRef, exactly 3 SintExpr0",
                commands.get(0).command.toString());

        assertSintexprBounds(0, "[" +
                "[SintExpr0$0, A_c$0], " +
                "[SintExpr0$1, A_c$1], " +
                "[SintExpr0$2, A_c$2]" +
                "]");

        assertEquals("[(= (+ SintExpr0$0 2) 4), (= (+ SintExpr0$1 2) 4), (= (+ SintExpr0$2 2) 4)]",
                commands.get(0).smtExprs.toString());
    }
}
