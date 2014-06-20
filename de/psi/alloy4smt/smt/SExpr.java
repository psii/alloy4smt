package de.psi.alloy4smt.smt;

import java.util.Arrays;
import java.util.List;
import java.util.Vector;

public abstract class SExpr<V> {

    public static<V> SExpr<V> num(int i) {
        return new Symbol<V>(String.valueOf(i));
    }

    public static<V> SExpr<V> sym(String name) {
        return new Symbol<V>(name);
    }

    public static<V> SExpr<V> leaf(V leaf) {
        return new Leaf<V>(leaf);
    }

    public static<V> SExpr<V> call(String funcName, SExpr<V>... args) {
        List<SExpr<V>> l = new Vector<SExpr<V>>();
        l.add(new Symbol<V>(funcName));
        l.addAll(Arrays.asList(args));
        return new SList<V>(l);
    }

    public static<V> SExpr<V> and(SExpr<V>... args) {
        if (args.length > 1) {
            return call("and", args);
        } else if (args.length == 1) {
            return args[0];
        } else {
            return new Symbol<V>("#t");
        }
    }

    public static<V> SExpr<V> add(SExpr<V>... args) {
        return SExpr.<V>call("+", args);
    }

    public static<V> SExpr<V> eq(SExpr<V>... args) {
        return SExpr.<V>call("=", args);
    }

    public static class Symbol<V> extends SExpr<V> {
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

        @Override
        public <T> T accept(Visitor<V, T> vtVisitor) {
            return vtVisitor.visit(this);
        }
    }

    public static class Leaf<V> extends SExpr<V> {
        private final V value;

        public Leaf(V item) {
            this.value = item;
        }

        public V getValue() {
            return value;
        }

        @Override
        public <T> T accept(Visitor<V, T> vtVisitor) {
            return vtVisitor.visit(this);
        }

        @Override
        public String toString() {
            return value.toString();
        }
    }

    public static class SList<V> extends SExpr<V> {
        private final List<SExpr<V>> items;

        public SList(List<SExpr<V>> items) {
            this.items = items;
        }

        public List<SExpr<V>> getItems() {
            return items;
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

        @Override
        public <T> T accept(Visitor<V, T> vtVisitor) {
            return vtVisitor.visit(this);
        }
    }
    
    public static abstract class Visitor<V, T> {
        public final T visitThis(SExpr<V> x) { return x.accept(this); }

        public abstract T visit(Symbol<V> vSymbol);

        public abstract T visit(Leaf<V> vLeaf);

        public abstract T visit(SList<V> vsList);
    }

    public abstract<T> T accept(Visitor<V, T> vtVisitor);

}
