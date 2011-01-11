package de.psi.alloy4smt.ast;

import java.util.List;
import java.util.Vector;

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
    public ConstList<Sig> sigs;
    
    public static interface SigBuilder {
    	public Sig make() throws Err;
    }
    
    private Sig currentSig;
    private Sig.Field currentField;
    private Sig.PrimSig intref;

    private IntRefPreprocessor() {
    }

    public static IntRefPreprocessor processModule(CompModule module) throws Err {
    	final IntRefPreprocessor result = new IntRefPreprocessor();
    	final SigBuilder builder = new SigBuilder() {
			@Override
			public Sig make() throws Err {
				String label = result.currentSig.label + "$" + result.currentField.label + "$IntRef0";
				return new Sig.PrimSig(label, result.intref);
			}
		};
		
		List<Sig> sigs = new Vector<Sig>();
		for (Sig s: module.getAllReachableSigs()) {
			if (s.builtin) {
				sigs.add(s);
			} else {
				sigs.add(result.convertSig(s, builder));
			}
		}
		
		result.sigs = ConstList.make(sigs);
		
        return result;
    }
    
    private Sig convertSig(Sig sig, SigBuilder builder) throws Err {
    	boolean newSigNeeded = false;
    	Sig newSig = new Sig.PrimSig(sig.label);
    	
    	currentSig = sig;
    	
    	for (Sig.Field field: sig.getFields()) {
    		currentField = field;
    		Expr oldExpr = field.decl().expr;
    		Expr newExpr = convertExpr(oldExpr, builder);
    		newSig.addTrickyField(field.pos, field.isPrivate, null, null, field.isMeta, 
    				              new String[] { field.label }, newExpr);
    		if (oldExpr != newExpr)
    			newSigNeeded = true;
    	}
    	
    	return newSigNeeded ? newSig : sig;
    }

    public static Expr convertExpr(Expr expr, SigBuilder builder) throws Err {
        Expr result = expr;

        if (expr == Sig.SIGINT) {
            result = builder.make();
        } else if (expr instanceof ExprUnary) {
            ExprUnary unary = (ExprUnary) expr;
            Expr newSub = convertExpr(unary.sub, builder);
            if (newSub != unary.sub) {
                result = unary.op.make(unary.pos, newSub);
            }
        } else if (expr instanceof ExprBinary) {
            ExprBinary binary = (ExprBinary) expr;
            Expr newLeft = convertExpr(binary.left, builder);
            Expr newRight = convertExpr(binary.right, builder);
            if (newLeft != binary.left || newRight != binary.right) {
                result = binary.op.make(binary.pos, binary.closingBracket, newLeft, newRight);
            }
        }

        return result;
    }
}
