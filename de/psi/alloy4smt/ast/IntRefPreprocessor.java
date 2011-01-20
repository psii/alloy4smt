package de.psi.alloy4smt.ast;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
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
    public final Sig.PrimSig intref;
    public final ConstList<Command> commands;

    
    public static interface SigBuilder {
    	public Sig makeSig() throws Err;
    	
    	public void addFactor(Sig factor);
    }
        
    private IntRefPreprocessor(Computer computer) {
    	sigs = computer.sigs.makeConst();
    	intref = computer.intref;
    	commands = computer.commands.makeConst();
    }
    
    private static class Computer implements SigBuilder {
    	private ConstList<Command> oldcommands;
    	private Sig currentSig;
    	private Sig.Field currentField;
    	private Sig.Field lastfield = null;
    	private int fieldcnt = 0;
    	private Map<Command, Integer> factors;
    	private Map<Command, List<CommandScope>> newscopes;
    	private List<Sig> newintrefs;
    	
    	public TempList<Sig> sigs;
    	public Sig.PrimSig intref;
    	public TempList<Command> commands;
    	
    	public Computer(CompModule module) throws Err {
    		sigs = new TempList<Sig>();
    		intref = (PrimSig) Helpers.getSigByName(module.getAllReachableSigs(), "intref/IntRef");
    		oldcommands = module.getAllCommands();
    		commands = new TempList<Command>();
    		factors = new HashMap<Command, Integer>();
    		newscopes = new HashMap<Command, List<CommandScope>>();
    		newintrefs = new Vector<Sig>();
    		
    		for (Command c: oldcommands) {
    			newscopes.put(c, new Vector<CommandScope>());
    		}
    		    		
    		for (Sig s: module.getAllReachableSigs()) {
    			if (s.builtin) {
    				sigs.add(s);
    			} else {
    				sigs.add(convertSig(s));
    			}
    		}
    		
    		for (Command c: oldcommands) {
    			TempList<CommandScope> scopes = new TempList<CommandScope>();
    			scopes.addAll(c.scope);
    			scopes.addAll(newscopes.get(c));
    			commands.add(c.change(scopes.makeConst()));
    		}
    	}
    	
    	@Override
    	public void addFactor(Sig factor) {
    		for (Command c: oldcommands) {
    			CommandScope scope = c.getScope(factor);
    			if (scope != null)
    				factors.put(c, factors.get(c) * c.getScope(factor).endingScope);
    		}
    	}
    	
    	private void resetFactors() {
    		for (Command c: oldcommands) {
    			factors.put(c, 1);
    		}
    	}

    	@Override
    	public Sig makeSig() throws Err {
    		if (lastfield != currentField) {
    			fieldcnt = 0;
    			lastfield = currentField;
    		} else {
    			fieldcnt++;
    		}
    		String label = currentSig.label + "$" + currentField.label + "$IntRef" + fieldcnt;
    		Sig sig = new Sig.PrimSig(label, intref);
			newintrefs.add(sig);
			
			return sig;
    	}
    	
    	private void integrateNewIntRefSigs() throws ErrorSyntax {
    		for (Sig sig: newintrefs) {
	    		for (Command c: oldcommands) {
	    			newscopes.get(c).add(new CommandScope(sig, false, factors.get(c)));
	    		}
	    		sigs.add(sig);
    		}
    		newintrefs.clear();
    	}
    	
        private Sig convertSig(Sig sig) throws Err {
        	boolean newSigNeeded = false;
        	Sig newSig = new Sig.PrimSig(sig.label);        	
        	
        	currentSig = sig;
        	
        	for (Sig.Field field: sig.getFields()) {
            	resetFactors();
            	addFactor(sig);
            	
        		currentField = field;
        		Expr oldExpr = field.decl().expr;
        		Expr newExpr = convertExpr(oldExpr, this);
        		newSig.addTrickyField(field.pos, field.isPrivate, null, null, field.isMeta, 
        				              new String[] { field.label }, newExpr);
        		if (oldExpr != newExpr)
        			newSigNeeded = true;
        		
        		integrateNewIntRefSigs();
        	}
        	
        	return newSigNeeded ? newSig : sig;
        }
    }

    public static IntRefPreprocessor processModule(CompModule module) throws Err {
    	return new IntRefPreprocessor(new Computer(module));
    }

    public static Expr convertExpr(Expr expr, SigBuilder builder) throws Err {
        Expr result = expr;

        if (expr == Sig.SIGINT) {
            result = builder.makeSig();
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
        } else if (expr instanceof Sig) {
        	builder.addFactor((Sig) expr);
        }

        return result;
    }
}
