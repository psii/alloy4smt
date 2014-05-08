package de.psi.alloy4smt.ast;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstList.TempList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.Attr;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprITE;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprLet;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQt;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Type;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitQuery;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;


public class IntRefPreprocessor {
    public final Sig.PrimSig intref;
    public final ConstList<PreparedCommand> commands;
    public final ConstList<Sig> sigs;

    public static String atomize(Sig sig, int id) {
    	String label = sig.label;
    	if (label.startsWith("this/")) {
    		label = label.substring(5);
    	}
    	return label + "$" + id;
    }


    private IntRefPreprocessor(Computer computer) throws Err {
    	intref = computer.intref;
    	sigs = computer.sigs.makeConst();
    	
    	TempList<PreparedCommand> tmpCommands = new TempList<PreparedCommand>();
    	for (int i = 0; i < computer.commands.size(); ++i) {
    		final IntexprSigBuilder isbuilder = new IntexprSigBuilder(computer.commands.get(i), intref);
    		final FactRewriter.Result rewriteres = FactRewriter.rewrite(computer.commands.get(i).formula, isbuilder);
        	final Command command = isbuilder.getModifiedCommand().change(rewriteres.newformula);
    		final TempList<PreparedCommand.IntrefSigRecord> l = new TempList<PreparedCommand.IntrefSigRecord>();
    		l.addAll(computer.intrefRecords.get(i));
    		l.addAll(isbuilder.getIntexprRecords());
    		final TempList<Sig> esigs = new TempList<Sig>();
    		esigs.addAll(sigs);
    		esigs.addAll(isbuilder.getIntExprSigs());
    		
    		tmpCommands.add(new PreparedCommand(command, rewriteres.hysatexprs, l.makeConst(), esigs.makeConst(), intref));
    	}
    	
    	commands = tmpCommands.makeConst();
    }
    
    private IntRefPreprocessor(CompModule module) {
    	intref = null;
    	sigs = module.getAllReachableSigs();
    	
    	TempList<PreparedCommand> tmpCommands = new TempList<PreparedCommand>();
    	for (Command c : module.getAllCommands()) {
    		tmpCommands.add(new PreparedCommand(c, sigs));
    	}
    	
    	commands = tmpCommands.makeConst();
    }
    

    private static class Computer {
    	private ConstList<Command> oldcommands;
    	private Map<Command, List<CommandScope>> newscopes;
    	private Map<Command, TempList<PreparedCommand.IntrefSigRecord>> tmpIntrefRecords;
    	private Map<PrimSig, PrimSig> old2newsigs;
    	private Map<Field, Field> old2newfields;

    	public TempList<Sig> sigs;
    	public Sig.PrimSig intref;
    	public TempList<Command> commands;
    	public TempList<ConstList<PreparedCommand.IntrefSigRecord>> intrefRecords;
    	
    	public Computer(CompModule module, Sig.PrimSig intref) throws Err {
    		this.intref = intref;
    		sigs = new TempList<Sig>();
    		old2newsigs = new HashMap<PrimSig, PrimSig>();
    		old2newfields = new HashMap<Field, Field>();
    		oldcommands = module.getAllCommands();
    		commands = new TempList<Command>();
    		newscopes = new HashMap<Command, List<CommandScope>>();
    		tmpIntrefRecords = new HashMap<Command, TempList<PreparedCommand.IntrefSigRecord>>();
    		intrefRecords = new TempList<ConstList<PreparedCommand.IntrefSigRecord>>();
    		
    		for (Command c: oldcommands) {
    			newscopes.put(c, new Vector<CommandScope>());
    			tmpIntrefRecords.put(c, new TempList<PreparedCommand.IntrefSigRecord>());
    		}

            // Initialize old2newsigs map. All Sigs except builtin and intref are cloned.
            // old2newsigs is a map which gets used for the later step convertSig
            // TODO: What about Subsetsigs?
    		for (Sig s: module.getAllReachableSigs()) {
    			if (s == intref) {
    				old2newsigs.put(intref, intref);
    				for (Field f : s.getFields())
    					old2newfields.put(f, f);
    			} else if (isSmtInt(s)) {
    				Attr[] attrs = new Attr[1];
    				PrimSig newsig = new PrimSig(s.label, s.attributes.toArray(attrs));
    				old2newsigs.put((PrimSig) s, newsig);
    			}
    		}

            // Converts all Sigs. The mapping between old and new sigs is already in place.
            // Now the new Sigs have to be populated with data/fields.
    		for (Sig s: module.getAllReachableSigs()) {
    			if (s.builtin || s == intref) {
    				sigs.add(s);
    			} else {
    				sigs.add(convertSig(s));
    			}
    		}

            // Rewrite step of the facts. Each Sig and its fields have a new instance. Now the facts have
            // to get updated and added to the new Sigs.
    		for (Sig s: module.getAllReachableSigs()) {
    			if (!s.builtin)
    				convertSigFacts(s);
    		}

            // Rewrite of the formula generated by each command.
    		for (Command c: oldcommands) {
    			TempList<CommandScope> scopes = new TempList<CommandScope>();
    			for (CommandScope scope : c.scope) {
    				scopes.add(new CommandScope(old2newsigs.get(scope.sig), scope.isExact, scope.endingScope));
    			}
    			scopes.addAll(newscopes.get(c));
                ExprRewriter rewriter = new ExprRewriter(intref, old2newsigs, old2newfields);
    			commands.add(c.change(scopes.makeConst()).change(rewriter.visitThis(c.formula)));
    			intrefRecords.add(tmpIntrefRecords.get(c).makeConst());
    		}
    	}

        private boolean isSmtInt(Sig s) {
            return !s.builtin && s instanceof PrimSig;
            //return !s.builtin && s.label.equals("Sint");
        }

        private Sig convertSig(Sig sig) throws Err {
        	final Sig newSig = old2newsigs.get(sig);        	

        	for (Sig.Field field: sig.getFields()) {
                final ExprRewriter rewriter = new ExprRewriter(intref, sig, field, old2newsigs, old2newfields);
        		final Expr newExpr = rewriter.visitThis(field.decl().expr);
        		final Field[] newField = newSig.addTrickyField(
        				field.pos, field.isPrivate, null, null, field.isMeta, 
        				new String[] { field.label }, newExpr);
        		old2newfields.put(field, newField[0]);

                for (PrimSig primSig: rewriter.newintrefs) {
                    for (Command c: oldcommands) {
                        final int scope = rewriter.getFactor(c);
                        newscopes.get(c).add(new CommandScope(primSig, true, scope));
                        tmpIntrefRecords.get(c).add(new PreparedCommand.IntrefSigRecord(primSig, null, null, scope));
                    }
                    sigs.add(primSig);
                }
        	}
        	
        	return newSig;
        }
        
        private void convertSigFacts(Sig sig) throws Err {
        	final Sig newSig = old2newsigs.get(sig);
        	
        	for (Expr fact : sig.getFacts()) {
        		newSig.addFact(new ExprRewriter(intref, old2newsigs, old2newfields).visitThis(fact));
        	}
        }

        private static class ExprRewriter extends VisitReturn<Expr> {

            private final PrimSig intref;
            private final Sig currentSig;
            private final Field currentField;
            private final Map<PrimSig, PrimSig> old2newsigs;
            private final Map<Field, Field> old2newfields;

            private Field lastfield = null;

            public List<PrimSig> newintrefs;
            public List<Sig> factors;

            ExprRewriter(PrimSig intref, Map<PrimSig, PrimSig> old2newsigs, Map<Field, Field> old2newfields) {
                this.intref = intref;
                this.currentSig = null;
                this.currentField = null;
                this.old2newsigs = old2newsigs;
                this.old2newfields = old2newfields;
                this.newintrefs = null;
                this.factors = new Vector<Sig>();
            }

            ExprRewriter(PrimSig intref, Sig currentSig, Field currentField, Map<PrimSig, PrimSig> old2newsigs, Map<Field, Field> old2newfields) {
                this.intref = intref;
                this.currentSig = currentSig;
                this.currentField = currentField;
                this.old2newsigs = old2newsigs;
                this.old2newfields = old2newfields;
                this.newintrefs = new Vector<PrimSig>();
                this.factors = new Vector<Sig>();
                addFactor(currentSig);
            }

            private Sig makeSig() throws Err {
                if (lastfield != currentField) {
                    lastfield = currentField;
                } else {
                    throw new ErrorFatal(currentField.pos, "unsupported decl");
                }
                String label = currentSig.label + "_" + currentField.label + "_IntRef";
                PrimSig sig = new Sig.PrimSig(label, intref);
                newintrefs.add(sig);

                return sig;
            }

            private void addFactor(Sig x) {
                this.factors.add(x);
            }

            public int getFactor(Command c) {
                int result = 1;
                for (Sig s : factors) {
                    result *= Helpers.getScope(c, s);
                }
                return result;
            }

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
    
    private static class IntexprSigBuilder {
    	
    	private LinkedHashMap<ExprVar, Expr> freeVars;
    	private Context ctx;
    	
    	private static class Context {
    		public int id = 0;
    		public PrimSig intref;
    		public Sig.Field aqclass;
    		public List<PreparedCommand.IntrefSigRecord> records = new Vector<PreparedCommand.IntrefSigRecord>();
    		public Command command;
    	}
    	
    	public IntexprSigBuilder(Command command, PrimSig intref) {
    		ctx = new Context();
    		ctx.command = command;
    		ctx.intref = intref;
    		ctx.aqclass = Helpers.getFieldByName(intref.getFields(), "aqclass");
    		freeVars = new LinkedHashMap<ExprVar, Expr>();
		}
    	
    	private IntexprSigBuilder(IntexprSigBuilder other) {
    		ctx = other.ctx;
    		freeVars = new LinkedHashMap<ExprVar, Expr>(other.freeVars);
    	}
    	
    	public Pair<PreparedCommand.IntrefSigRecord, Expr> make(Expr intrefExpr) throws Err {
    		final PrimSig intexprsig = new PrimSig("IntExpr" + ctx.id++, ctx.intref);
    		final Set<ExprVar> usedFreeVars = FreeVarFinder.find(intrefExpr);
    		final Expr right = ExprBinary.Op.JOIN.make(null, null, intrefExpr, ctx.aqclass);
    		Expr left;
    		Sig.Field mapfield = null;
    		List<Sig> dependencies = new Vector<Sig>();
    		int instances = 1;
    		
    		if (!usedFreeVars.isEmpty()) {
    			Type type = null;
    			for (ExprVar var : usedFreeVars) {
    				final Expr e = freeVars.get(var);
    				if (type == null) {
    					type = e.type();
    				} else {
    					type = e.type().product(type);
    				}
    			}
                mapfield = intexprsig.addField("map", type.toExpr());
    			
    			for (List<PrimSig> ss : type.fold()) {
    				int ssinst = 1;
    				for (PrimSig sig : ss) {
    					ssinst *= Helpers.getScope(ctx.command, sig);
    					dependencies.add(0, sig);
    				}
    				instances *= ssinst;
    			}
    			
    			Expr mapjoin = mapfield;
    			for (ExprVar var : usedFreeVars) {
    				mapjoin = ExprBinary.Op.JOIN.make(null, null, mapjoin, var);
    			}
    			
    			left = ExprBinary.Op.JOIN.make(null, null, mapjoin, ctx.aqclass);
    		} else {
    			left = ExprBinary.Op.JOIN.make(null, null, intexprsig, ctx.aqclass);
    		}
    		
    		PreparedCommand.IntrefSigRecord result = new PreparedCommand.IntrefSigRecord(intexprsig, mapfield, ConstList.make(dependencies), instances);
    		
    		ctx.command = ctx.command.change(intexprsig, true, instances);
    		ctx.records.add(result);
    		
    		return new Pair<PreparedCommand.IntrefSigRecord, Expr>(result, ExprBinary.Op.EQUALS.make(null, null, left, right));
    	}
    	
    	public IntexprSigBuilder addFreeVariables(ConstList<Decl> decls) {
    		IntexprSigBuilder result = new IntexprSigBuilder(this);
    		
    		for (Decl d : decls) {
    			for (ExprHasName ehn : d.names) {
    				result.freeVars.put((ExprVar) ehn, d.expr);
    			}
    		}
    		
    		return result;
    	}
    	
    	public Command getModifiedCommand() {
    		return ctx.command;
    	}
    	
    	public List<PreparedCommand.IntrefSigRecord> getIntexprRecords() {
    		return ctx.records;
    	}
    	
    	public List<PrimSig> getIntExprSigs() {
    		List<PrimSig> result = new Vector<PrimSig>();
    		for (PreparedCommand.IntrefSigRecord record : ctx.records) {
    			result.add(record.sig);
    		}
    		return result;
    	}    	
    }
    
    private static class FreeVarFinder extends VisitQuery<Object> {
    	private Set<ExprVar> freeVars = new LinkedHashSet<ExprVar>();

		@Override
		public Object visit(ExprVar x) throws Err {
			freeVars.add(x);
			return super.visit(x);
		}
		
		private FreeVarFinder() {
		}
		
		public static Set<ExprVar> find(Expr x) throws Err {
			FreeVarFinder finder = new FreeVarFinder();
			finder.visitThis(x);
			return finder.freeVars;
		}
    }
    
    private static class IntExprHandler extends VisitReturn<TempList<String>> {
    	
    	private List<Expr> facts;
    	private IntexprSigBuilder builder;
    	private boolean cast2intSeen;
    	
    	public IntExprHandler(IntexprSigBuilder isb) {
			this.facts = new Vector<Expr>();
			this.builder = isb;
			this.cast2intSeen = false;
		}
    	
    	public Expr getFacts() {
    		return ExprList.make(null, null, ExprList.Op.AND, facts);
    	}
    	
    	private void throwUnsupportedOperator(Expr x) throws Err {
    		throw new ErrorSyntax(x.pos, "HySAT does not support this operator.");
    	}

		@Override
		public TempList<String> visit(ExprUnary x) throws Err {
			TempList<String> result;
			
			if (x.op == ExprUnary.Op.CAST2INT) {
				cast2intSeen = true;
				result = visitThis(x.sub);
				cast2intSeen = false;
			} else {	
				final TempList<String> sub = visitThis(x.sub);
				switch (x.op) {
				case NOOP: result = sub; break;
				default:
					throw new AssertionError();
				}
			}

			return result;
		}

		@Override
		public TempList<String> visit(ExprBinary x) throws Err {
			if (cast2intSeen && x.op == ExprBinary.Op.JOIN) {
				Pair<PreparedCommand.IntrefSigRecord, Expr> result = builder.make(x);
				facts.add(result.b);
				return new TempList<String>(result.a.getAtoms());
			} else {
				final TempList<String> left = visitThis(x.left);
				final TempList<String> right = visitThis(x.right);
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
				
				TempList<String> result = new TempList<String>();
				for (String l : left.makeConst()) {
					for (String r : right.makeConst()) {
						result.add("(" + l + " " + op + " " + r + ")");
					}
				}
				return result;
			}
		}

		@Override
		public TempList<String> visit(ExprConstant x) throws Err {
			if (x.op == ExprConstant.Op.NUMBER) {
				return new TempList<String>(String.valueOf(x.num));
			} else {
				throw new ErrorSyntax(x.pos, "Constant not convertible to HySAT");
			}
		}

		@Override
		public TempList<String> visit(ExprList x) throws Err {
			throw new AssertionError();
		}

		@Override
		public TempList<String> visit(ExprCall x) throws Err {
			throw new AssertionError();
		}

		@Override
		public TempList<String> visit(ExprITE x) throws Err {
			throw new AssertionError();
		}

		@Override
		public TempList<String> visit(ExprLet x) throws Err {
			throw new AssertionError();
		}

		@Override
		public TempList<String> visit(ExprQt x) throws Err {
			throw new AssertionError();
		}

		@Override
		public TempList<String> visit(ExprVar x) throws Err {
			throw new AssertionError();
		}

		@Override
		public TempList<String> visit(Sig x) throws Err {
			throw new AssertionError();
		}

		@Override
		public TempList<String> visit(Field x) throws Err {
			throw new AssertionError();
		}

    }
    
    private static class FactRewriter extends VisitReturn<Expr> {

        public static class Result {
            public final Expr newformula;
            public final ConstList<String> hysatexprs;

            public Result(Expr newformula, ConstList<String> hysatexprs) {
                this.newformula = newformula;
                this.hysatexprs = hysatexprs;
            }
        }
    	
    	private IntexprSigBuilder intexprBuilder;
    	private TempList<String> hysatexprs;
    	
    	private FactRewriter(IntexprSigBuilder builder) {
    		hysatexprs = new TempList<String>();
    		intexprBuilder = builder;
		}
    	
    	public static Result rewrite(Expr expr, IntexprSigBuilder builder) throws Err {
    		FactRewriter rewriter = new FactRewriter(builder);
    		Expr rewritten = rewriter.visitThis(expr);
    		return new Result(rewritten, rewriter.hysatexprs.makeConst());
    	}
    	
		@Override
		public Expr visit(ExprBinary x) throws Err {
			Expr result = null;

            // TODO: change this to check for our custom SMTInt datatype
			if (x.left.type().is_int() && x.right.type().is_int()) {
				final IntExprHandler ieh = new IntExprHandler(intexprBuilder);
				final TempList<String> hexpr = ieh.visitThis(x);
				hysatexprs.addAll(hexpr.makeConst());
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
			final IntexprSigBuilder tmpold = intexprBuilder;
			intexprBuilder = tmpold.addFreeVariables(x.decls);
			Expr sub = visitThis(x.sub);
			intexprBuilder = tmpold;
			return x.op.make(x.pos, x.closingBracket, x.decls, sub);
		}

		@Override
		public Expr visit(ExprUnary x) throws Err {
			final Expr sub = visitThis(x.sub);
			if (x.op == ExprUnary.Op.CAST2INT) {
				throw new AssertionError();
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
