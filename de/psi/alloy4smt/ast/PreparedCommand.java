package de.psi.alloy4smt.ast;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

import java.util.List;
import java.util.Vector;

/**
* Created by psi on 08.05.14.
*/
public class PreparedCommand {
    public final Command command;
    public final ConstList<String> hysatExprs;
    public final ConstList<IntrefSigRecord> intrefRecords;
    public final ConstList<Sig> sigs;
    public final Sig.PrimSig intref;

    public PreparedCommand(Command command, ConstList<String> hysatExprs, ConstList<IntrefSigRecord> intrefRecords,
                           ConstList<Sig> sigs, Sig.PrimSig intref) {
        this.command = command;
        this.hysatExprs = hysatExprs;
        this.intrefRecords = intrefRecords;
        this.sigs = sigs;
        this.intref = intref;
    }

    public PreparedCommand(Command command, ConstList<Sig> sigs) {
        this.command = command;
        this.hysatExprs = null;
        this.intrefRecords = null;
        this.sigs = sigs;
        this.intref = null;
    }

    public ConstList<String> getIntrefAtoms() {
        ConstList.TempList<String> result = new ConstList.TempList<String>();
        for (IntrefSigRecord record : intrefRecords) {
            result.addAll(record.getAtoms());
        }
        return result.makeConst();
    }

    public TupleSet getIntRefEqualsTupleSet(TupleFactory factory) {
        final List<String> atoms = getIntrefAtoms();
        final int numatoms = atoms.size();
        TupleSet result = factory.noneOf(2);

        for (int i = 0; i < numatoms; ++i) {
            for (int j = i + 1; j < numatoms; ++j) {
                result.add(factory.tuple(atoms.get(i), atoms.get(j)));
            }
        }

        return result;
    }

    public static class IntrefSigRecord {
    	public final Sig.PrimSig sig;
    	public final Sig.Field mapfield;
    	public final ConstList<Sig> dependencies;
    	public final int instances;

    	public IntrefSigRecord(Sig.PrimSig intexpr, Sig.Field mapfield, ConstList<Sig> dependencies, int instances) {
    		this.sig = intexpr;
    		this.mapfield = mapfield;
    		this.dependencies = dependencies;
    		this.instances = instances;
    	}

    	public List<String> getAtoms() {
    		List<String> result = new Vector<String>();
    		for (int i = 0; i < instances; ++i) {
    			result.add(IntRefPreprocessor.atomize(sig, i));
    		}
    		return result;
    	}

    	private ConstList<Pair<Sig, Integer>> getDependencyScopes(Command command) {
    		ConstList.TempList<Pair<Sig, Integer>> result = new ConstList.TempList<Pair<Sig, Integer>>();
    		for (Sig sig : dependencies) {
    			result.add(new Pair<Sig, Integer>(sig, Helpers.getScope(command, sig)));
    		}
    		return result.makeConst();
    	}

    	public TupleSet getMapBounds(Command command, TupleFactory factory) {
    		TupleSet result = null;

    		if (mapfield != null) {
    			final ConstList<Pair<Sig, Integer>> depscopes = getDependencyScopes(command);
    			final int depsize = depscopes.size();
    			int[] sigids = new int[depsize + 1];
    			result = factory.noneOf(depsize + 1);
    			addMapBoundsTuples(factory, result, depscopes, 0, sigids);
    		}

    		return result;
    	}

    	private void addMapBoundsTuples(TupleFactory factory, TupleSet result,
    			                        ConstList<Pair<Sig, Integer>> depscopes, int depthlvl,
    			                        int[] sigids) {
    		if (depthlvl < depscopes.size()) {
    			final int scope = depscopes.get(depthlvl).b;
    			for (int i = 0; i < scope; ++i) {
    				sigids[depthlvl + 1] = i;
    				addMapBoundsTuples(factory, result, depscopes, depthlvl + 1, sigids);
    			}
    		} else {
    			List<String> tuple = new Vector<String>();
    			tuple.add(IntRefPreprocessor.atomize(sig, sigids[0]++));
    			for (int d = depscopes.size() - 1; d >= 0; --d) {
    				tuple.add(IntRefPreprocessor.atomize(depscopes.get(d).a, sigids[d + 1]));
    			}
    			result.add(factory.tuple(tuple));
    		}
    	}
    }
}
