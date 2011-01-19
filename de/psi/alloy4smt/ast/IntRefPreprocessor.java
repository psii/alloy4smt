package de.psi.alloy4smt.ast;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
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
    	public Sig make() throws Err;
    }
        
    private IntRefPreprocessor(Computer computer) {
    	sigs = computer.sigs.makeConst();
    	intref = computer.intref;
    	commands = computer.commands.makeConst();
    }
    
    private static class Computer {
    	private ConstList<Command> oldcommands;
    	private Sig currentSig;
    	private Sig.Field currentField;
    	private Map<Command, List<CommandScope>> newscopes;
    	
    	public TempList<Sig> sigs;
    	public Sig.PrimSig intref;
    	public TempList<Command> commands;
    	
    	public Computer(CompModule module) throws Err {
    		sigs = new TempList<Sig>();
    		intref = (PrimSig) Helpers.getSigByName(module.getAllReachableSigs(), "intref/IntRef");
    		oldcommands = module.getAllCommands();
    		commands = new TempList<Command>();
    		newscopes = new HashMap<Command, List<CommandScope>>();
    		
    		for (Command c: oldcommands) {
    			newscopes.put(c, new Vector<CommandScope>());
    		}
    		
    		final SigBuilder builder = new SigBuilder() {
        		private int cnt = 0;
        		private Sig.Field lastfield = null;
        		
    			@Override
    			public Sig make() throws Err {
    				if (lastfield != currentField) {
    					cnt = 0;
    					lastfield = currentField;
    				} else {
    					cnt++;
    				}
    				String label = currentSig.label + "$" + currentField.label + "$IntRef" + cnt;
    				return addIntRefSig(label);
    			}    			
    		};
    		
    		for (Sig s: module.getAllReachableSigs()) {
    			if (s.builtin) {
    				sigs.add(s);
    			} else {
    				sigs.add(convertSig(s, builder));
    			}
    		}
    		
    		for (Command c: oldcommands) {
    			TempList<CommandScope> scopes = new TempList<CommandScope>();
    			scopes.addAll(c.scope);
    			scopes.addAll(newscopes.get(c));
    			commands.add(c.change(scopes.makeConst()));
    		}
    	}
    	
    	private Sig addIntRefSig(String label) throws Err {
    		Sig sig = new Sig.PrimSig(label, intref);
    		sigs.add(sig);
    		
    		for (Command c: oldcommands) {
    			CommandScope scope = c.getScope(currentSig);
    			newscopes.get(c).add(new CommandScope(sig, false, scope.endingScope));
    		}
    		
    		return sig;
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
    }

    public static IntRefPreprocessor processModule(CompModule module) throws Err {
    	return new IntRefPreprocessor(new Computer(module));
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
