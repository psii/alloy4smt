package de.psi.alloy4smt.ast;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;

/**
 * Created by IntelliJ IDEA.
 * User: psi
 * Date: 10.01.11
 * Time: 15:41
 * To change this template use File | Settings | File Templates.
 */
public class IntRefPreprocessor {
    public final ConstList<Sig> sigs;

    private IntRefPreprocessor(ConstList<Sig> sigs) {
        this.sigs = sigs;
    }

    public static IntRefPreprocessor processModule(CompModule module) {
        return new IntRefPreprocessor(module.getAllReachableSigs());
    }

    public static void convertAndAttachField(Sig.Field field, Sig sig) throws Err {
        //sig.addDefinedField(field.pos(), field.isPrivate, field.isMeta, field.label, field.decl().expr);
        sig.addTrickyField(field.pos(), field.isPrivate, null, null, field.isMeta, new String[] {field.label}, field.decl().expr);
    }
}
