package de.psi.alloy4smt.ast;


import de.psi.alloy4smt.smt.SExpr;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class SmtPreprocessor {
    public static PreparedCommand build(Command c, ConstList<Sig> allReachableSigs) throws Err {
        ConversionContext ctx = new ConversionContext(c, allReachableSigs);
        for (Sig s : allReachableSigs) ctx.mapSig(s);
        Expr newformula = FormulaRewriter.rewrite(ctx, c.formula);
        return new PreparedCommand(c.change(ctx.getScopes()).change(ctx.getAdditionalFacts().and(newformula)),
                ctx.getAllSigs(), ctx.getSExprs());
    }

//    private static class SintRefAssign {
//        public final Sig sig;
//        public final Iterable<Sig> dependencies;
//        public final SExpr sexpr;
//    }

    private static class ConversionContext {
        public final Sig sigSint;
        private final int defaultScope;
        private final Sig.PrimSig sigSintref;
        public final Sig.Field aqclass;
        private final Map<Sig, Sig> newsigmap = new HashMap<Sig, Sig>();
        private final Map<Sig.Field, Sig.Field> newfieldmap = new HashMap<Sig.Field, Sig.Field>();
        private final Map<Sig, CommandScope> scopemap = new HashMap<Sig, CommandScope>();
        private final ConstList.TempList<Sig> allsigs = new ConstList.TempList<Sig>();
        private final ConstList.TempList<CommandScope> scopes = new ConstList.TempList<CommandScope>();
        private final ConstList.TempList<SExpr> sexprs = new ConstList.TempList<SExpr>();
        private final ConstList.TempList<String> smtvars = new ConstList.TempList<String>();
        private final ConstList.TempList<Expr> newfacts = new ConstList.TempList<Expr>();

        private int exprcnt = 0;

        public ConversionContext(Command command, ConstList<Sig> sigs) throws Err {
            sigSint = Helpers.getSigByName(sigs, "smtint/Sint");
            sigSintref = (Sig.PrimSig) Helpers.getSigByName(sigs, "smtint/SintRef");
            aqclass = Helpers.getFieldByName(sigSintref.getFields(), "aqclass");
            if (sigSint == null || sigSintref == null || aqclass == null)
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

        public ConstList<SExpr> getSExprs() {
            return sexprs.makeConst();
        }

        public Expr getAdditionalFacts() {
            return ExprList.make(null, null, ExprList.Op.AND, newfacts.makeConst());
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

        public void addGlobalFact(SExpr sexpr) {
            sexprs.add(sexpr);
        }

        public Expr makeRefSig(SExpr sexpr) throws Err {
            StringBuilder sb = new StringBuilder();
            sb.append("SintExpr");
            sb.append(exprcnt++);
            Sig ref = new Sig.PrimSig(sb.toString(), sigSintref);
            addRefSig(ref, new Vector<Sig>());
            SExpr symb = SExpr.sym(sb.toString() + "$0");
            addGlobalFact(SExpr.eq(symb, sexpr));
            return ref;
        }

        public SExpr makeAlias(Expr expr) throws Err {
            if (!isSintRefExpr(expr)) throw new AssertionError();
            StringBuilder sb = new StringBuilder();
            sb.append("SintExpr");
            sb.append(exprcnt);
            exprcnt++;
            smtvars.add(sb.toString());
            Sig ref = new Sig.PrimSig(sb.toString(), sigSintref);
            addRefSig(ref, new Vector<Sig>());
            SExpr var = SExpr.sym(sb.toString() + "$0");
            newfacts.add(ref.join(aqclass).equal(expr.join(aqclass)));
            return var;
        }

        public boolean isSintRefExpr(Expr expr) {
            return expr.type().isSubtypeOf(sigSintref.type());
        }

        public boolean isSintExpr(Expr expr) {
            return expr.type().equals(sigSint.type());
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

        public static Expr rewrite(ConversionContext ctx, Expr formula) throws Err {
            FormulaRewriter rewriter = new FormulaRewriter(ctx);
            // We don't use `apply` here, because FormulaRewriter is also used by
            // SintExprRewriter to rewrite subexpressions.
            return rewriter.visitThis(formula);
        }

        private final ConversionContext ctx;

        private FormulaRewriter(ConversionContext ctx) {
            this.ctx = ctx;
        }
       
        private Expr apply(Expr expr) throws Err {
            if (ctx.isSintExpr(expr)) {
                return SintExprRewriter.rewrite(ctx, expr);
            } else {
                return visitThis(expr);
            }
        }

        @Override public Expr visit(ExprBinary x) throws Err {
            return x.op.make(x.pos, x.closingBracket, apply(x.left), apply(x.right));
        }
        @Override public Expr visit(ExprUnary x) throws Err {
            return x.op.make(x.pos, apply(x.sub));
        }
        @Override public Expr visit(ExprITE x) throws Err {
            return ExprITE.make(x.pos, apply(x.cond), apply(x.left), apply(x.right));
        }
        @Override public Expr visit(ExprList x) throws Err {
            ConstList.TempList<Expr> args = new ConstList.TempList<Expr>();
            for (Expr e: x.args) {
                args.add(apply(e));
            }
            return ExprList.make(x.pos, x.closingBracket, x.op, args.makeConst());
        }
        @Override public Expr visit(ExprConstant x) throws Err {
            return x;
        }
        @Override public Expr visit(ExprVar x) throws Err {
            return x;
        }
        @Override public Expr visit(ExprLet x) throws Err {
            return ExprLet.make(x.pos, x.var, apply(x.expr), apply(x.sub));
        }
        @Override public Expr visit(Sig x) throws Err {
            return ctx.mapSig(x);
        }
        @Override public Expr visit(Sig.Field x) throws Err {
            return ctx.mapField(x);
        }

        @Override public Expr visit(ExprCall x) throws Err {
            if (x.fun.label.equals("smtint/gt")) {
                return SintExprRewriter.rewriteFun(ctx, x, ">");
            } else {
                ConstList.TempList<Expr> args = new ConstList.TempList<Expr>();
                for (Expr e : x.args) {
                    args.add(visitThis(e));
                }
                return ExprCall.make(x.pos, x.closingBracket, x.fun, args.makeConst(), x.extraWeight);
            }
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            // TODO: handle quantification correctly w.r.t. Sintexprs
            return x.op.make(x.pos, x.closingBracket, x.decls, apply(x.sub));
        }

    }


    private static class SintExprRewriter extends VisitReturn<SExpr> {

        public static Expr rewrite(ConversionContext ctx, Expr expr) throws Err {
            SintExprRewriter rewriter = new SintExprRewriter(ctx);
            SExpr result = rewriter.visitThis(expr);
            return ctx.makeRefSig(result).join(ctx.aqclass);
        }

        public static Expr rewriteFun(ConversionContext ctx, ExprCall x, String smtOp) throws Err {
            SintExprRewriter rewriter = new SintExprRewriter(ctx);
            Vector<SExpr> sargs = new Vector<SExpr>();
            for (Expr arg : x.args) {
                sargs.add(rewriter.visitThis(arg));
            }
            SExpr result = SExpr.call(smtOp, sargs.toArray(new SExpr[]{}));
            ctx.addGlobalFact(result);
            return ExprConstant.TRUE;
        }

        private final ConversionContext ctx;

        private SintExprRewriter(ConversionContext ctx) {
            this.ctx = ctx;
        }

        private SExpr unexpected() {
            throw new AssertionError("unexpected node");
        }

        @Override
        public SExpr visit(ExprCall x) throws Err {
            if (x.fun.label.equals("smtint/gt")) {
                return SExpr.call(">", visitThis(x.args.get(0)), visitThis(x.args.get(1)));
            } else if (x.fun.label.equals("smtint/plus")) {
                return SExpr.call("+", visitThis(x.args.get(0)), visitThis(x.args.get(1)));
            } else if (x.fun.label.equals("smtint/const")) {
                Expr arg = x.args.get(0);
                int c;
                if (arg instanceof ExprConstant)
                    c = ((ExprConstant) arg).num();
                else if (arg instanceof ExprUnary) {
                    ExprUnary cast = (ExprUnary) arg;
                    if (cast.op != ExprUnary.Op.CAST2SIGINT) throw new AssertionError();
                    c = ((ExprConstant) cast.sub).num();
                } else {
                    throw new AssertionError();
                }
                return SExpr.num(c);
            } else {
                throw new AssertionError("User defined Sint functions not yet supported");
            }
        }

        private SExpr makeAlias(Expr x) throws Err {
            return ctx.makeAlias(FormulaRewriter.rewrite(ctx, x));
        }

        @Override public SExpr visit(ExprBinary x) throws Err {
            return makeAlias(x);
        }
        @Override public SExpr visit(ExprList x) throws Err {
            return unexpected();
        }
        @Override public SExpr visit(ExprConstant x) throws Err {
            return unexpected();
        }
        @Override public SExpr visit(ExprITE x) throws Err {
            return unexpected();
        }
        @Override public SExpr visit(ExprLet x) throws Err {
            return unexpected();
        }
        @Override public SExpr visit(ExprQt x) throws Err {
            return unexpected();
        }
        @Override public SExpr visit(ExprUnary x) throws Err {
            return unexpected();
        }
        @Override public SExpr visit(ExprVar x) throws Err {
            return unexpected();
        }
        @Override public SExpr visit(Sig x) throws Err {
            return unexpected();
        }
        @Override public SExpr visit(Sig.Field x) throws Err {
            return unexpected();
        }
    }

}
