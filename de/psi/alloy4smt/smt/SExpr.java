package de.psi.alloy4smt.smt;

import java.util.Arrays;
import java.util.List;
import java.util.Vector;

public abstract class SExpr {

    public static final SExpr TRUE = SExpr.sym("#t");

    public static SExpr num(int i) {
        return new Symbol(String.valueOf(i));
    }

    public static SExpr sym(String name) {
        return new Symbol(name);
    }

    public static SExpr call(String funcName, SExpr... args) {
        List<SExpr> l = new Vector<SExpr>();
        l.add(sym(funcName));
        l.addAll(Arrays.asList(args));
        return new SList(l);
    }

    public static SExpr and(SExpr... args) {
        if (args.length > 1) {
            return call("and", args);
        } else if (args.length == 1) {
            return args[0];
        } else {
            return TRUE;
        }
    }

    public static SExpr add(SExpr... args) {
        return call("+", args);
    }

    public static SExpr eq(SExpr... args) {
        return call("=", args);
    }

    public static class Symbol extends SExpr {
        private final String name;

        public Symbol(String name) {
            this.name = name;
        }

        public String getName() {
            return name;
        }

        @Override
        public String toString() {
            return name;
        }
    }

    public static class SList extends SExpr {
        private final List<SExpr> items;

        public SList(List<SExpr> items) {
            this.items = items;
        }

        @Override
        public String toString() {
            boolean first = true;
            StringBuilder sb = new StringBuilder();
            sb.append("(");
            for (SExpr expr : items) {
                if (first) first = false; else sb.append(" ");
                sb.append(expr.toString());
            }
            sb.append(")");
            return sb.toString();
        }
    }

}
