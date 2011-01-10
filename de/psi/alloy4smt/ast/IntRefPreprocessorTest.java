package de.psi.alloy4smt.ast;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import org.junit.Before;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * Created by IntelliJ IDEA.
 * User: psi
 * Date: 10.01.11
 * Time: 15:42
 * To change this template use File | Settings | File Templates.
 */
public class IntRefPreprocessorTest {

    private static final String doc =
            "sig X { v: Y }\n" +
            "sig Y { w: X ->one X }\n";

    private static final String doc2 =
            "sig X { v: Int }\n" +
            "sig Y { w: X ->one Int }\n";

    private static final String[] stdsigs = { "univ", "Int", "seq/Int", "String", "none" };

    private CompModule parseModule(String doc) throws Err {
        Map<String,String> fm = new HashMap<String, String>();
        fm.put("/tmp/x", doc);
        return CompUtil.parseEverything_fromFile(null, fm, "/tmp/x");
    }

    private static void assertStdSigsRetained(CompModule module, IntRefPreprocessor p) {
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
        CompModule module = parseModule(doc);
        IntRefPreprocessor p = IntRefPreprocessor.processModule(module);
        ConstList<Sig> msigs = module.getAllReachableSigs();
        ConstList<Sig> nsigs = p.sigs;

        assertEquals(msigs, nsigs);
        assertStdSigsRetained(module, p);
    }

    @Test
    public void convertSingleField() throws Err {
        CompModule module = parseModule(doc2);
        Sig sigX = getSigByName(module.getAllReachableSigs(), "this/X");
        Sig.Field fieldV = getFieldByName(sigX.getFields(), "v");
        assertNotNull(fieldV);

        Sig newSig = new Sig.PrimSig("this/NewX", Sig.UNIV);
        IntRefPreprocessor.convertAndAttachField(fieldV, newSig);
        Sig.Field newV = getFieldByName(newSig.getFields(), "v");
        assertNotNull(newV);

        assertEquals("{this/X->Int}", fieldV.type().toString());
        assertEquals("{this/NewX->Int}", newV.type().toString());
    }

    @Test
    public void convertIntSigs() throws Err {
        CompModule module = parseModule(doc2);
        IntRefPreprocessor p = IntRefPreprocessor.processModule(module);

        assertStdSigsRetained(module, p);

        Sig sigX = getSigByName(p.sigs, "this/X");
        for (Decl d: sigX.getFieldDecls()) {
            assertTrue(d.hasName("v"));
        }
    }
}
