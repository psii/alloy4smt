package de.psi.alloy4smt.ast;


import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.*;

import java.util.HashMap;
import java.util.Map;

public class SmtPreprocessor {
    public static PreparedCommand build(Command c, ConstList<Sig> allReachableSigs) throws Err {
        ConversionContext ctx = new ConversionContext(c, allReachableSigs);
        for (Sig s : allReachableSigs) ctx.mapSig(s);
        return new PreparedCommand(c.change(ctx.getScopes()), ctx.getAllSigs());
    }

    private static class ConversionContext {
        public final Sig sigSint;
        private final int defaultScope;
        private final Sig.PrimSig sigSintref;
        private final Map<Sig, Sig> newsigmap = new HashMap<Sig, Sig>();
        private final Map<Sig.Field, Sig.Field> newfieldmap = new HashMap<Sig.Field, Sig.Field>();
        private final Map<Sig, CommandScope> scopemap = new HashMap<Sig, CommandScope>();
        private final ConstList.TempList<Sig> allsigs = new ConstList.TempList<Sig>();
        private final ConstList.TempList<CommandScope> scopes = new ConstList.TempList<CommandScope>();

        public ConversionContext(Command command, ConstList<Sig> sigs) throws Err {
            sigSint = Helpers.getSigByName(sigs, "smtint/Sint");
            sigSintref = (Sig.PrimSig) Helpers.getSigByName(sigs, "smtint/SintRef");
            if (sigSint == null || sigSintref == null)
                throw new AssertionError();
            addSigMapping(sigSintref, sigSintref);
            for (Sig.Field f : sigSintref.getFields())
                newfieldmap.put(f, f);

            defaultScope = command.overall < 0 ? 1 : command.overall;

            // Populate scope map for the old sigs
            for (CommandScope scope : command.scope) {
                scopemap.put(scope.sig, scope);
            }

            // Populate the scope list for the new sigs
            for (CommandScope scope : command.scope) {
                Sig s = mapSig(scope.sig);
                scopes.add(new CommandScope(s, scope.isExact, scope.endingScope));
            }
        }

        public ConstList<Sig> getAllSigs() {
            return allsigs.makeConst();
        }

        public ConstList<CommandScope> getScopes() {
            return scopes.makeConst();
        }

        private void addSigMapping(Sig oldsig, Sig newsig) {
            newsigmap.put(oldsig, newsig);
            allsigs.add(newsig);
        }

        public Sig mapSig(Sig old) throws Err {
            Sig result;
            if (!newsigmap.containsKey(old)) {
                if (old instanceof Sig.PrimSig) {
                    Attr[] attrs = new Attr[1];
                    result = new Sig.PrimSig(old.label, old.attributes.toArray(attrs));
                    addSigMapping(old, result);
                    for (Sig.Field field : old.getFields()) {
                        final FieldRewriter.Result rewriteResult = FieldRewriter.rewrite(this, old, field);
                        final Sig.Field[] newField = result.addTrickyField(field.pos, field.isPrivate, null, null, field.isMeta, new String[] {field.label}, rewriteResult.field);
                        newfieldmap.put(field, newField[0]);
                        if (rewriteResult.ref != null)
                            addRefSig(rewriteResult.ref, rewriteResult.refdeps);
                    }
                } else if (old instanceof Sig.SubsetSig) {
                    throw new AssertionError("not handled yet");
                } else {
                    throw new AssertionError();
                }
            } else {
                result = newsigmap.get(old);
            }
            return result;
        }

        public Sig.Field mapField(Sig.Field old) {
            Sig.Field field = newfieldmap.get(old);
            if (field == null) throw new AssertionError();
            return field;
        }

        public void addRefSig(Sig ref, Iterable<Sig> dependencies) throws Err {
            allsigs.add(ref);
            int refscope = 1;
            for (Sig depsig : dependencies) {
                CommandScope scope = scopemap.get(depsig);
                if (scope != null) {
                    refscope *= scope.endingScope;
                } else if (depsig.isOne != null || depsig.isLone != null) {
                    refscope *= 1;
                } else {
                    refscope *= defaultScope;
                }
            }
            scopes.add(new CommandScope(ref, true, refscope));
        }

    }


    private static class FieldRewriter extends VisitReturn<Expr> {
        private final ConversionContext ctx;
        private final Sig sig;
        private final Sig.Field field;
        private final ConstList.TempList<Sig> visitedsigs = new ConstList.TempList<Sig>();
        private Sig.PrimSig ref = null;

        public static class Result {
            public final Sig ref;
            public final Expr field;
            public final ConstList<Sig> refdeps;

            public Result(Sig ref, Expr field, ConstList<Sig> refdeps) {
                this.ref = ref;
                this.field = field;
                this.refdeps = refdeps;
            }
        }

        public static Result rewrite(ConversionContext ctx, Sig sig, Sig.Field field) throws Err {
            FieldRewriter rewriter = new FieldRewriter(ctx, sig, field);
            Expr expr = rewriter.visitThis(field.decl().expr);
            return new Result(rewriter.ref, expr, rewriter.visitedsigs.makeConst());
        }

        private FieldRewriter(ConversionContext ctx, Sig sig, Sig.Field field) {
            this.ctx = ctx;
            this.sig = sig;
            this.field = field;
            visitedsigs.add(sig);
        }

        private Expr unexpected() {
            throw new AssertionError("Unexpected field expression!");
        }

        @Override public Expr visit(ExprList x) throws Err {
            return unexpected();
        }
        @Override public Expr visit(ExprCall x) throws Err {
            return unexpected();
        }
        @Override public Expr visit(ExprConstant x) throws Err {
            return unexpected();
        }
        @Override public Expr visit(ExprITE x) throws Err {
            return unexpected();
        }
        @Override public Expr visit(ExprLet x) throws Err {
            return unexpected();
        }
        @Override public Expr visit(ExprQt x) throws Err {
            return unexpected();
        }
        @Override public Expr visit(ExprVar x) throws Err {
            return unexpected();
        }

        @Override public Expr visit(ExprUnary x) throws Err {
            return x.op.make(x.pos, visitThis(x.sub));
        }

        @Override public Expr visit(ExprBinary x) throws Err {
            return x.op.make(x.pos, x.closingBracket, visitThis(x.left), visitThis(x.right));
        }

        @Override
        public Expr visit(Sig x) throws Err {
            Sig s;
            if (x == ctx.sigSint) {
                if (ref != null) throw new AssertionError();
                String label = sig.label + "_" + field.label + "_SintRef";
                ref = new Sig.PrimSig(label, ctx.sigSintref);
                s = ref;
            } else {
                visitedsigs.add(x);
                s = ctx.mapSig(x);
            }
            return s;
        }

        @Override
        public Expr visit(Sig.Field x) throws Err {
            return ctx.mapField(x);
        }
    }


    private static class FormulaRewriter extends VisitReturn<Expr> {

        @Override
        public Expr visit(ExprBinary x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprCall x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            return null;
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            return null;
        }

        @Override
        public Expr visit(Sig x) throws Err {
            return null;
        }

        @Override
        public Expr visit(Sig.Field x) throws Err {
            return null;
        }
    }
}
