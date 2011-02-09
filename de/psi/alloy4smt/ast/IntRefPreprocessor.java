package de.psi.alloy4smt.ast;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4compiler.ast.Attr;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprITE;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprLet;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQt;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;


public class IntRefPreprocessor {
    public final Sig.PrimSig intref;
    public final ConstList<CmdBundle> commands;
    public final ConstList<Sig> sigs;
	
	
	public static class CmdBundle {
		public final Command command;
		public final ConstList<String> hysatExprs;
		public final ConstList<String> intrefAtoms;
		public final ConstList<Sig> sigs;
		public final Sig.PrimSig intref;
		
		public CmdBundle(Command command, ConstList<String> hysatExprs, ConstList<String> intrefAtoms,
				ConstList<Sig> sigs, Sig.PrimSig intref) {
			this.command = command;
			this.hysatExprs = hysatExprs;
			this.intrefAtoms = intrefAtoms;
			this.sigs = sigs;
			this.intref = intref;
		}
		
		public CmdBundle(Command command, ConstList<Sig> sigs) {
			this.command = command;
			this.hysatExprs = null;
			this.intrefAtoms = null;
			this.sigs = sigs;
			this.intref = null;
		}

		public TupleSet getIntRefEqualsTupleSet(TupleFactory factory) {
			final int numatoms = intrefAtoms.size();
			TupleSet result = factory.noneOf(2);
			
			for (int i = 0; i < numatoms; ++i) {
				for (int j = i + 1; j < numatoms; ++j) {
					result.add(factory.tuple(intrefAtoms.get(i), intrefAtoms.get(j)));
				}
			}
			
			return result;
		}
	}

        
    private IntRefPreprocessor(Computer computer) throws Err {
    	intref = computer.intref;
    	sigs = computer.sigs.makeConst();
    	
    	TempList<CmdBundle> tmpCommands = new TempList<CmdBundle>();
    	for (int i = 0; i < computer.commands.size(); ++i) {
    		final FactRewriter rewriter = FactRewriter.rewrite(computer.commands.get(i).formula, intref);
        	final Command command = computer.commands.get(i).change(rewriter.getFacts());
    		final TempList<String> l = new TempList<String>();
    		l.addAll(computer.intrefAtoms.get(i));
    		l.addAll(rewriter.getIntExprAtoms());
    		final TempList<Sig> esigs = new TempList<Sig>();
    		esigs.addAll(sigs);
    		esigs.addAll(rewriter.getIntExprSigs());
    		
    		tmpCommands.add(new CmdBundle(command, rewriter.getHysatExprs(), l.makeConst(), esigs.makeConst(), intref));
    	}
    	
    	commands = tmpCommands.makeConst();
    }
    
    private IntRefPreprocessor(CompModule module) {
    	intref = null;
    	sigs = module.getAllReachableSigs();
    	
    	TempList<CmdBundle> tmpCommands = new TempList<CmdBundle>();
    	for (Command c : module.getAllCommands()) {
    		tmpCommands.add(new CmdBundle(c, sigs));
    	}
    	
    	commands = tmpCommands.makeConst();
    }
    
    private static class Computer {
    	private ConstList<Command> oldcommands;
    	private Sig currentSig;
    	private Sig.Field currentField;
    	private Sig.Field lastfield = null;
    	private int fieldcnt = 0;
    	private Map<Command, Integer> factors;
    	private Map<Command, List<CommandScope>> newscopes;
    	private Map<Command, TempList<String>> tmpIntrefAtoms;
    	private Map<PrimSig, PrimSig> old2newsigs;
    	private Map<Field, Field> old2newfields;
    	private List<Sig> newintrefs;
    	
    	public TempList<Sig> sigs;
    	public Sig.PrimSig intref;
    	public TempList<Command> commands;
    	public TempList<ConstList<String>> intrefAtoms;
    	
    	public Computer(CompModule module, Sig.PrimSig intref) throws Err {
    		this.intref = intref;
    		sigs = new TempList<Sig>();
    		old2newsigs = new HashMap<PrimSig, PrimSig>();
    		old2newfields = new HashMap<Field, Field>();
    		oldcommands = module.getAllCommands();
    		commands = new TempList<Command>();
    		factors = new HashMap<Command, Integer>();
    		newscopes = new HashMap<Command, List<CommandScope>>();
    		newintrefs = new Vector<Sig>();
    		tmpIntrefAtoms = new HashMap<Command, TempList<String>>();
    		intrefAtoms = new TempList<ConstList<String>>();
    		
    		for (Command c: oldcommands) {
    			newscopes.put(c, new Vector<CommandScope>());
    			tmpIntrefAtoms.put(c, new TempList<String>());
    		}
    		
    		for (Sig s: module.getAllReachableSigs()) {
    			if (!s.builtin && s instanceof PrimSig) {
    				Attr[] attrs = new Attr[1];
    				PrimSig newsig = new PrimSig(s.label, s.attributes.toArray(attrs));
    				old2newsigs.put((PrimSig) s, newsig);
    			}
    		}
    		    		
    		for (Sig s: module.getAllReachableSigs()) {
    			if (s.builtin) {
    				sigs.add(s);
    			} else {
    				sigs.add(convertSig(s));
    			}
    		}
    		
    		for (Sig s: module.getAllReachableSigs()) {
    			if (!s.builtin)
    				convertSigFacts(s);
    		}
    		
    		for (Command c: oldcommands) {
    			TempList<CommandScope> scopes = new TempList<CommandScope>();
    			scopes.addAll(c.scope);
    			scopes.addAll(newscopes.get(c));
    			commands.add(c.change(scopes.makeConst()).change(EXPR_REWRITER.visitThis(c.formula)));
    			intrefAtoms.add(tmpIntrefAtoms.get(c).makeConst());
    		}
    	}
    	
    	public void addFactor(Sig factor) {
    		for (Command c: oldcommands) {
    			CommandScope scope = c.getScope(factor);
    			int mult;
    			if (scope != null) {
    				mult = c.getScope(factor).endingScope;
    			} else if (factor.isOne != null || factor.isLone != null) {
    				mult = 1;
    			} else {
    				mult = c.overall < 0 ? 1 : c.overall;
    			}
    			factors.put(c, factors.get(c) * mult);
    		}
    	}
    	
    	private void resetFactors() {
    		for (Command c: oldcommands) {
    			factors.put(c, 1);
    		}
    	}

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
    	
    	private static String atomize(Sig sig, int id) {
    		String label = sig.label;
    		if (label.startsWith("this/"))
    			label = label.substring(5);
    		return label + "$" + id;
    	}
    	
    	private void integrateNewIntRefSigs() throws ErrorSyntax {
    		for (Sig sig: newintrefs) {
	    		for (Command c: oldcommands) {
	    			final int scope = factors.get(c);
	    			newscopes.get(c).add(new CommandScope(sig, true, scope));
	    			for (int i = 0; i < scope; ++i) {
	    				tmpIntrefAtoms.get(c).add(atomize(sig, i));
	    			}
	    		}
	    		sigs.add(sig);
    		}
    		newintrefs.clear();
    	}
    	
    	private final ExprRewriter EXPR_REWRITER = new ExprRewriter();
    	
        private Sig convertSig(Sig sig) throws Err {
        	final Sig newSig = old2newsigs.get(sig);        	
        	
        	currentSig = sig;
        	
        	for (Sig.Field field: sig.getFields()) {
            	resetFactors();
            	addFactor(sig);
            	
        		currentField = field;
        		final Expr newExpr = EXPR_REWRITER.visitThis(field.decl().expr);
        		final Field[] newField = newSig.addTrickyField(
        				field.pos, field.isPrivate, null, null, field.isMeta, 
        				new String[] { field.label }, newExpr);
        		old2newfields.put(field, newField[0]);
        		
        		integrateNewIntRefSigs();
        	}
        	
        	return newSig;
        }
        
        private void convertSigFacts(Sig sig) throws Err {
        	final Sig newSig = old2newsigs.get(sig);
        	
        	for (Expr fact : sig.getFacts()) {
        		newSig.addFact(EXPR_REWRITER.visitThis(fact));
        	}
        }

        private class ExprRewriter extends VisitReturn<Expr> {

			@Override
			public Expr visit(ExprBinary x) throws Err {
				return x.op.make(x.pos, x.closingBracket, visitThis(x.left), visitThis(x.right));
			}

			@Override
			public Expr visit(ExprList x) throws Err {
				List<Expr> args = new Vector<Expr>();
				for (Expr a : x.args) args.add(visitThis(a));
				return ExprList.make(x.pos, x.closingBracket, x.op, args);
			}

			@Override
			public Expr visit(ExprCall x) throws Err {
				return x;
			}

			@Override
			public Expr visit(ExprConstant x) throws Err {
				return x;
			}

			@Override
			public Expr visit(ExprITE x) throws Err {
				return ExprITE.make(x.pos, visitThis(x.cond), visitThis(x.left), visitThis(x.right));
			}

			@Override
			public Expr visit(ExprLet x) throws Err {
				return ExprLet.make(x.pos, x.var, visitThis(x.expr), visitThis(x.sub));
			}

			@Override
			public Expr visit(ExprQt x) throws Err {
				List<Decl> decls = new Vector<Decl>();
				for (Decl d : x.decls) {
					decls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.names, visitThis(d.expr)));
				}
				return x.op.make(x.pos, x.closingBracket, decls, visitThis(x.sub));
			}

			@Override
			public Expr visit(ExprUnary x) throws Err {
				return x.op.make(x.pos, visitThis(x.sub));
			}

			@Override
			public Expr visit(ExprVar x) throws Err {
				return x;
			}

			@Override
			public Expr visit(Sig x) throws Err {
				Sig s;
				if (x == Sig.SIGINT) {
					s = makeSig();
				} else {
					s = old2newsigs.get(x);
					if (s == null) s = x;
					addFactor(x);
				}
				return s;
			}

			@Override
			public Expr visit(Field x) throws Err {
				Field f = old2newfields.get(x);
				if (f == null) throw new AssertionError();
				return f;
			}
        	
        }

    }
    
    private static interface IntexprSigBuilder {
    	public Sig.PrimSig make() throws Err;
    }
    
    private static class IntExprHandler extends VisitReturn<String> {
    	
    	private List<Expr> facts;
    	private Sig.Field aqclass;
    	private IntexprSigBuilder builder;
    	
    	public IntExprHandler(Sig.Field aqclass, IntexprSigBuilder isb) {
			this.facts = new Vector<Expr>();
			this.aqclass = aqclass;
			this.builder = isb;
		}
    	
    	public Expr getFacts() {
    		return ExprList.make(null, null, ExprList.Op.AND, facts);
    	}
    	
    	private void throwUnsupportedOperator(Expr x) throws Err {
    		throw new ErrorSyntax(x.pos, "HySAT does not support this operator.");
    	}

		@Override
		public String visit(ExprUnary x) throws Err {
			String result;
			
			if (x.op == ExprUnary.Op.CAST2INT) {
				final Sig.PrimSig exprsig = builder.make();
				final Expr a = ExprBinary.Op.JOIN.make(null, null, exprsig, aqclass);
				final Expr b = ExprBinary.Op.JOIN.make(null, null, x.sub, aqclass);
				facts.add(ExprBinary.Op.EQUALS.make(null, null, a, b));
				result = exprsig.label;				
			} else {	
				final String sub = visitThis(x.sub);
				switch (x.op) {
				case NOT: result = "!" + sub; break;
				case NOOP: result = sub; break;
				default:
					throw new AssertionError();
				}
			}

			return result;
		}

		@Override
		public String visit(ExprBinary x) throws Err {
			final String left = visitThis(x.left);
			final String right = visitThis(x.right);
			String op = null;
			
			switch (x.op) {
			case GT:         op = ">"; break;
			case LT:         op = "<"; break;
			case GTE:        op = ">="; break;
			case LTE:        op = "<="; break;
			case EQUALS:     op = "="; break;
			case MINUS:      op = "-"; break;
			case MUL:        op = "*"; break;
			case NOT_EQUALS: op = "!="; break;
			case NOT_GT:     op = "<="; break;
			case NOT_LT:     op = ">="; break;
			case NOT_GTE:    op = "<"; break;
			case NOT_LTE:    op = ">"; break;
			case PLUS:       op = "+"; break;
			
			default:
				throwUnsupportedOperator(x);
			}

			return "(" + left + " " + op + " " + right + ")";
		}

		@Override
		public String visit(ExprConstant x) throws Err {
			if (x.op == ExprConstant.Op.NUMBER) {
				return String.valueOf(x.num);
			} else {
				throw new ErrorSyntax(x.pos, "Constant not convertible to HySAT");
			}
		}

		@Override
		public String visit(ExprList x) throws Err {
			throw new AssertionError();
		}

		@Override
		public String visit(ExprCall x) throws Err {
			throw new AssertionError();
		}

		@Override
		public String visit(ExprITE x) throws Err {
			throw new AssertionError();
		}

		@Override
		public String visit(ExprLet x) throws Err {
			throw new AssertionError();
		}

		@Override
		public String visit(ExprQt x) throws Err {
			throw new AssertionError();
		}

		@Override
		public String visit(ExprVar x) throws Err {
			throw new AssertionError();
		}

		@Override
		public String visit(Sig x) throws Err {
			throw new AssertionError();
		}

		@Override
		public String visit(Field x) throws Err {
			throw new AssertionError();
		}

    }
    
    private static class FactRewriter extends VisitReturn<Expr> {
    	
    	private final Sig.PrimSig intref;
    	private final Sig.Field aqclass;
    	private final IntexprSigBuilder intexprBuilder;
    	private List<Sig.PrimSig> intexprs;
    	
    	private Expr rewritten;
    	private TempList<String> hysatexprs;
    	
    	private FactRewriter(Sig.PrimSig intref_) {
    		intref = intref_;
    		aqclass = Helpers.getFieldByName(intref.getFields(), "aqclass");
    		intexprs = new Vector<Sig.PrimSig>();
    		hysatexprs = new TempList<String>();
    		intexprBuilder = new IntexprSigBuilder() {
    			private int id = 0;
				@Override
				public PrimSig make() throws Err {
					final PrimSig result = new PrimSig("intexpr_" + id++, intref, Attr.ONE);
					intexprs.add(result);
					return result;
				}
			};
		}
    	
    	public static FactRewriter rewrite(Expr expr, Sig.PrimSig intref) throws Err {
    		FactRewriter rewriter = new FactRewriter(intref);
    		rewriter.rewritten = rewriter.visitThis(expr);
    		return rewriter;
    	}
    	
    	public Expr getFacts() {
    		return rewritten;
    	}
    	
    	public ConstList<String> getHysatExprs() {
    		return hysatexprs.makeConst();
    	}
    	
    	public ConstList<String> getIntExprAtoms() {
    		TempList<String> result = new TempList<String>();
    		for (Sig.PrimSig sig : intexprs) {
    			result.add(sig.label + "$0");
    		}
    		return result.makeConst();
    	}
    	
    	public ConstList<PrimSig> getIntExprSigs() {
    		return ConstList.make(intexprs);
    	}

		@Override
		public Expr visit(ExprBinary x) throws Err {
			Expr result = null;
			
			if (x.left.type().is_int && x.right.type().is_int) {
				final IntExprHandler ieh = new IntExprHandler(aqclass, intexprBuilder);
				final String hexpr = ieh.visitThis(x);
				hysatexprs.add(hexpr);
				result = ieh.getFacts();
			} else {
				final Expr left = visitThis(x.left);
				final Expr right = visitThis(x.right);
				result = x.op.make(x.pos, x.closingBracket, left, right);					
			}
			
			return result;
		}

		@Override
		public Expr visit(ExprList x) throws Err {
			TempList<Expr> args = new TempList<Expr>();
			for (Expr e: x.args) {
				args.add(visitThis(e));
			}
			return ExprList.make(x.pos, x.closingBracket, x.op, args.makeConst());
		}

		@Override
		public Expr visit(ExprCall x) throws Err {
			TempList<Expr> args = new TempList<Expr>();
			for (Expr e: x.args) {
				args.add(visitThis(e));
			}
			return ExprCall.make(x.pos, x.closingBracket, x.fun, args.makeConst(), x.extraWeight);
		}

		@Override
		public Expr visit(ExprConstant x) throws Err {
			return x;
		}

		@Override
		public Expr visit(ExprITE x) throws Err {
			Expr cond = visitThis(x.cond);
			Expr left = visitThis(x.left);
			Expr right = visitThis(x.right);
			return ExprITE.make(x.pos, cond, left, right);
		}

		@Override
		public Expr visit(ExprLet x) throws Err {
			Expr sub = visitThis(x.sub);
			return ExprLet.make(x.pos, x.var, x.expr, sub);
		}

		@Override
		public Expr visit(ExprQt x) throws Err {
			Expr sub = visitThis(x.sub);
			return x.op.make(x.pos, x.closingBracket, x.decls, sub);
		}

		@Override
		public Expr visit(ExprUnary x) throws Err {
			final Expr sub = visitThis(x.sub);
			if (x.op == ExprUnary.Op.CAST2INT) {
				throw new AssertionError();
//				Sig.PrimSig exprsig = new Sig.PrimSig("intexpr_0", intref, Attr.ONE);
//				intexprs.add(exprsig);
//				return ExprBinary.Op.JOIN.make(null, null, sub, aqclass);
			} else {
				return x.op.make(x.pos, sub);
			}
		}

		@Override
		public Expr visit(ExprVar x) throws Err {
			return x;
		}

		@Override
		public Expr visit(Sig x) throws Err {
			return x;
		}

		@Override
		public Expr visit(Field x) throws Err {
			return x;
		}
    	
    }
    

    public static IntRefPreprocessor processModule(CompModule module) throws Err {
    	final Sig.PrimSig intref = (Sig.PrimSig) Helpers.getSigByName(module.getAllReachableSigs(), "intref/IntRef");
    	if (intref != null) {
    		final Computer computer = new Computer(module, intref);
    		return new IntRefPreprocessor(computer);
    	} else {
    		return new IntRefPreprocessor(module);
    	}
    }

}
