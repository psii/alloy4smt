package de.psi.alloy4smt.ast;

import java.util.HashMap;
import java.util.Map;

import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.TupleSet;
import de.psi.alloy4smt.hysat.HysatSolver;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.BoundsComputer;
import edu.mit.csail.sdg.alloy4compiler.translator.ScopeComputer;
import edu.mit.csail.sdg.alloy4compiler.translator.Simplifier;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

public final class Translator extends TranslateAlloyToKodkod {
	
	public static final String intrefmod = 
		"module util/intref\n" +
		"abstract sig IntRef { aqclass: IntRef }\n";
	
	public static A4Solution execute(String document) throws Err {
		Map<String, String> fm = new HashMap<String, String>();
		fm.put("/tmp/x", document);
		fm.put("/tmp/util/intref.als", intrefmod);
		
		final CompModule module = CompUtil.parseEverything_fromFile(null, fm, "/tmp/x");
		final IntRefPreprocessor pp = IntRefPreprocessor.processModule(module);
		final A4Options opt = new A4Options();
		opt.recordKodkod = true;
		opt.tempDirectory = "/tmp";
		opt.solverDirectory = "/tmp";
		opt.solver = SatSolver.SAT4J;
		opt.skolemDepth = 4;
		
		return execute(null, opt, pp.commands.get(0));
	}
	
	public static A4Solution execute(A4Reporter rep, A4Options opt, IntRefPreprocessor.CmdBundle bundle) throws Err {
		rep = rep == null ? A4Reporter.NOP : rep;
		final Iterable<Sig> sigs = bundle.sigs;
		final Command cmd = bundle.command;
		final ConstList<String> hyexprs = bundle.hysatExprs;
		final ConstList<String> intrefatoms = hyexprs != null ? bundle.intrefAtoms : null;
		final Pair<A4Solution, ScopeComputer> pair = ScopeComputer.compute(rep, opt, sigs, cmd);
		
		BoundsComputer.compute(rep, pair.a, pair.b, sigs);
		
		if (hyexprs != null) {
			Sig.Field equalsfield = bundle.intref.addField("equals", bundle.intref.setOf());
			TupleSet equalsupper = bundle.getIntRefEqualsTupleSet(pair.a.getFactory());
			pair.a.addField(equalsfield, pair.a.addRel("IntRef/equals", null, equalsupper));
		}
		
		Translator tr = null;
		try {	
			tr = new Translator(rep, cmd, opt, pair.a);
			pair.a.solver.options().setSolver(new SATFactory() {
				@Override
				public SATSolver instance() {
					HysatSolver solver = new HysatSolver();
					if (hyexprs != null) {
						for (String atom : intrefatoms) {
							solver.addHysatVariable(atom, -1000000, 1000000);
						}
						for (String expr : hyexprs) {
							solver.addHysatExpr(expr);
						}
					}
					return solver;
				}

				@Override  public boolean prover() { return false; }
				@Override  public boolean minimizer() { return false; }
				@Override  public boolean incremental() { return false; }
				@Override  public String toString() { return "HySAT solver"; }
			});
			
			tr.makeFacts(cmd.formula);
			return tr.frame.solve(rep, cmd, new Simplifier(), true);
		} catch (HigherOrderDeclException ex) {
            Pos p = tr!=null ? tr.frame.kv2typepos(ex.decl().variable()).b : Pos.UNKNOWN;
            throw new ErrorType(p, "Analysis cannot be performed since it requires higher-order quantification that could not be skolemized.");			
		} catch (Throwable ex) {			
            if (ex instanceof Err) throw (Err)ex; else throw new ErrorFatal("Unknown exception occurred: "+ex, ex);
		}
	}

	private Translator(A4Reporter rep, Command cmd, A4Options opt, A4Solution frame) throws Err {
		super(rep, opt, frame, cmd);
	}
}
