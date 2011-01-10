package de.psi.alloy4smt.ast;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
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

    private static Expr convertExpr(Expr expr, Sig intRefSig) {
        Expr result = expr;

        if (expr == Sig.SIGINT) {
            result = intRefSig;
        } else if (expr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) expr;
            Expr newSub = convertExpr(unary.sub, intRefSig);
            if (newSub != unary.sub) {
                result = unary.op.make(unary.pos, newSub);
            }
        } else if (expr instanceof ExprBinary) {
            ExprBinary binary = (ExprBinary) expr;
            Expr newLeft = convertExpr(binary.left, intRefSig);
            Expr newRight = convertExpr(binary.right, intRefSig);
            if (newLeft != binary.left || newRight != binary.right) {
                result = binary.op.make(binary.pos, binary.closingBracket, newLeft, newRight);
            }
        }

        return result;
    }

    public static Sig.Field convertAndAttachField(Sig.Field field, Sig sig, Sig intRefSig) throws Err {
        return sig.addTrickyField(field.pos(), field.isPrivate, null, null,
                field.isMeta, new String[] {field.label}, convertExpr(field.decl().expr, intRefSig))[0];
    }
}
