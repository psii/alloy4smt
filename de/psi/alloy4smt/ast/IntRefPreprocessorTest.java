package de.psi.alloy4smt.ast;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
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
            "abstract sig IntRef {}\n";

    private static final String[] stdsigs = { "univ", "Int", "seq/Int", "String", "none" };

    private CompModule module;
    private IntRefPreprocessor.SigBuilder sigbuilder;

    @Before
    public void setUp() {
        module = null;
        
        sigbuilder = new IntRefPreprocessor.SigBuilder() {
        	private int id = 1;
			@Override
			public Sig make() throws Err {
				return new Sig.PrimSig("intref/IntRef" + id++);
			}
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

    private static Sig getSigByName(Iterable<Sig> sigs, String name) {
        Sig result = null;
        for (Sig s: sigs) {
            if (s.toString().equals(name)) {
                result = s;
                break;
            }
        }
        return result;
    }

    private static Sig.Field getFieldByName(Iterable<Sig.Field> fields, String name) {
        Sig.Field result = null;
        for (Sig.Field field: fields) {
            if (field.label.equals(name)) {
                result = field;
                break;
            }
        }
        return result;
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
        		p.sigs.contains(getSigByName(module.getAllReachableSigs(), "this/X")));
    }

    private void assertDeclConversion(String decl, String newDecl) throws Err {
        String modstr = "open util/intref\nsig A {}\nsig X { v: " + decl + " }\n";
		parseModule(modstr);
		Sig sig = getSigByName(module.getAllReachableSigs(), "this/X");
		Sig.Field field = getFieldByName(sig.getFields(), "v");
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

    @Test
    public void convertIntSigs() throws Err {
        parseModule("sig X { v: Int }\n");
        IntRefPreprocessor p = IntRefPreprocessor.processModule(module);

        assertStdSigsAreTheSame(module, p);
        assertFalse("A new instance for sig X should have been created",
        		p.sigs.contains(getSigByName(module.getAllReachableSigs(), "this/X")));

        Sig sigX = getSigByName(p.sigs, "this/X");
        assertEquals(1, sigX.getFieldDecls().size());
        Sig.Field fieldV = sigX.getFields().get(0);
        assertEquals("v", fieldV.label);
        assertEquals("one this/X$v$IntRef0", fieldV.decl().expr.toString());
        
    }
}
