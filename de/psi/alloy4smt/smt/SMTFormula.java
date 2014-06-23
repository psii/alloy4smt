package de.psi.alloy4smt.smt;

import java.util.List;
import java.util.Vector;

public class SMTFormula {
    private final List<SExpr<String>> constraints = new Vector<SExpr<String>>();
    private final List<String> boolvars = new Vector<String>();
    private final List<String> intvars = new Vector<String>();

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_NRA)\n");
        sb.append("(set-info :smt-lib-version 2.0)\n");
        for (String varname : boolvars) {
            sb.append("(declare-fun ");
            sb.append(varname);
            sb.append(" () Bool)\n");
        }
        for (String varname : intvars) {
            sb.append("(declare-fun ");
            sb.append(varname);
            sb.append(" () Int)\n");
        }
        for (SExpr<String> c : constraints)
            sb.append(c.toString() + "\n");
        return sb.toString();
    }

    public void addConstraint(SExpr<String> expr) {
        constraints.add(SExpr.call("assert", expr));
    }

    public void addBoolVariable(String varname) {
        boolvars.add(varname);
    }

    public void addIntegerVariable(String varname) {
        intvars.add(varname);
    }
}
