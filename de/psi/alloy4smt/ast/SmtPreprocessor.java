package de.psi.alloy4smt.ast;


import de.psi.alloy4smt.smt.SExpr;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.*;

import java.util.*;

public class SmtPreprocessor {
    public static PreparedCommand build(Command c, ConstList<Sig> allReachableSigs) throws Err {
        ConversionContext ctx = new ConversionContext(c, allReachableSigs);
        for (Sig s : allReachableSigs) ctx.mapSig(s);
        Expr newformula = FormulaRewriter.rewrite(ctx, c.formula);
        return new PreparedCommand(
                c.change(ctx.getScopes()).change(ctx.getAdditionalFacts().and(newformula)),
                ctx.getAllSigs(), ctx.sigSintref, ctx.getSExprs());
    }


    private static class ConversionContext {
        public final Sig sigSint;
        private final int defaultScope;
        public final Sig.PrimSig sigSintref;
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

        public int addRefSig(Sig ref, Iterable<Type> dependencies) throws Err {
            allsigs.add(ref);
            int refscope = 1;
            for (Type type : dependencies) {
                if (!type.hasArity(1)) throw new AssertionError();
                int unionscope = 0;
                for (List<Sig.PrimSig> l : type.fold()) {
                    if (l.size() != 1) throw new AssertionError();
                    Sig.PrimSig depsig = l.get(0);
                    CommandScope scope = scopemap.get(depsig);
                    if (scope != null) {
                        unionscope += scope.endingScope;
                    } else if (depsig.isOne != null || depsig.isLone != null) {
                        unionscope++;
                    } else {
                        unionscope += defaultScope;
                    }
                }
                refscope *= unionscope;
            }
            scopes.add(new CommandScope(ref, true, refscope));
            return refscope;
        }

        public void addGlobalFact(SExpr sexpr) {
            sexprs.add(sexpr);
        }

        public Expr makeRefSig(SExpr sexpr) throws Err {
            StringBuilder sb = new StringBuilder();
            sb.append("SintExpr");
            sb.append(exprcnt++);
            Sig ref = new Sig.PrimSig(sb.toString(), sigSintref);
            addRefSig(ref, new Vector<Type>());
            SExpr symb = SExpr.sym(sb.toString() + "$0");
            addGlobalFact(SExpr.eq(symb, sexpr));
            return ref;
        }

        /**
         * Creates an alias for an arbitrary complex SintRef expression w.r.t.
         * free variables.
         * @param expr Alloy Expression which must be of type SintRef
         * @return A pair (smtvar, subst) where smtvar contains a reference to the
         *         SMT variable as a SExpr. subst is the substitution for expr which
         *         references the newly generated SintExpr signature relation.
         * @throws Err
         */
        public Pair<ConstList<SExpr>, Expr> makeAlias(Expr expr) throws Err {
            if (!isSintRefExpr(expr)) throw new AssertionError();
            final Set<ExprVar> usedquantifiers = FreeVarFinder.find(expr);
            final List<Type> dependencies = new Vector<Type>();

            StringBuilder sb = new StringBuilder();
            sb.append("SintExpr");
            sb.append(exprcnt);
            exprcnt++;
            smtvars.add(sb.toString());
            Sig ref = new Sig.PrimSig(sb.toString(), sigSintref);

            Expr left;
            if (usedquantifiers.isEmpty()) {
                left = ref;
            } else {
                Type type = null;
                for (ExprVar var : usedquantifiers) {
                    if (!var.type().hasArity(1))
                        throw new AssertionError("Quantified variables with arity > 1 are not supported");
                    dependencies.add(var.type());
                    if (type == null)
                        type = var.type();
                    else
                        type = var.type().product(type);
                }

                left = ref.addField("map", type.toExpr());
                for (ExprVar var : usedquantifiers) {
                    left = left.join(var);
                }
            }
            int scope = addRefSig(ref, dependencies);
            ConstList.TempList<SExpr> vars = new ConstList.TempList<SExpr>();
            for (int i = 0; i < scope; ++i)
                vars.add(SExpr.sym(sb.toString() + "$" + i));
            return new Pair<ConstList<SExpr>, Expr>(vars.makeConst(), left.join(aqclass).equal(expr.join(aqclass)));
        }

        public boolean isSintRefExpr(Expr expr) {
            return expr.type().isSubtypeOf(sigSintref.type());
        }

        public boolean isSintExpr(Expr expr) {
            return expr.type().equals(sigSint.type());
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


    private static class FieldRewriter extends VisitReturn<Expr> {
        private final ConversionContext ctx;
        private final Sig sig;
        private final Sig.Field field;
        private final ConstList.TempList<Type> visitedsigs = new ConstList.TempList<Type>();
        private Sig.PrimSig ref = null;

        public static class Result {
            public final Sig ref;
            public final Expr field;
            public final ConstList<Type> refdeps;

            public Result(Sig ref, Expr field, ConstList<Type> refdeps) {
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
            visitedsigs.add(sig.type());
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
            // FIXME: Handle cases like A+B -> Sint (compared to A->B->Sint)
            if (!x.op.isArrow) throw new AssertionError();
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
                visitedsigs.add(x.type());
                s = ctx.mapSig(x);
            }
            return s;
        }

        @Override
        public Expr visit(Sig.Field x) throws Err {
            return ctx.mapField(x);
        }
    }



    private static class ExprRewriter extends VisitReturn<Expr> {

        public static Pair<Expr, AndExpr> rewrite(ConversionContext ctx, Expr expr) throws Err {
            ExprRewriter rewriter = new ExprRewriter(ctx);
            return new Pair<Expr, AndExpr>(rewriter.apply(expr), rewriter.result);
        }

        private final ConversionContext ctx;
        private final AndExpr result = new AndExpr();

        private ExprRewriter(ConversionContext ctx) {
            this.ctx = ctx;
        }

        private Expr apply(Expr expr) throws Err {
            if (ctx.isSintExpr(expr)) {
                Pair<Expr, AndExpr> rewrite = SintExprRewriter.rewrite(ctx, expr);
                result.add(rewrite.b);
                return rewrite.a;
            } else {
                return visitThis(expr);
            }
        }

        private Expr unexpected() {
            throw new AssertionError("unexpected node");
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
            ConstList.TempList<Expr> args = new ConstList.TempList<Expr>();
            for (Expr e : x.args) {
                args.add(visitThis(e));
            }
            return ExprCall.make(x.pos, x.closingBracket, x.fun, args.makeConst(), x.extraWeight);
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            return unexpected();
        }

    }


    private static class AndExpr {
        private final ConstList.TempList<Expr> result = new ConstList.TempList<Expr>();

        public void add(Expr expr) {
            if (expr.equals(ExprConstant.TRUE))
                return;
            result.add(expr);
        }

        public void add(AndExpr andExpr) {
            result.addAll(andExpr.result.makeConst());
        }

        public Expr getExpr() {
            if (result.size() == 0)
                return ExprConstant.TRUE;
            if (result.size() == 1)
                return result.get(0);

            Expr last = result.get(result.size() - 1);
            return ExprList.make(last.pos, last.closingBracket, ExprList.Op.AND, result.makeConst());
        }

    }


    private static class FormulaRewriter extends VisitReturn<Expr> {

        public static Expr rewrite(ConversionContext ctx, Expr formula) throws Err {
            if (!formula.type().is_bool) throw new AssertionError();
            FormulaRewriter rewriter = new FormulaRewriter(ctx);
            // We don't use `applyFormula` here, because FormulaRewriter is also used by
            // SintExprRewriter to rewrite subexpressions.
            return rewriter.visitThis(formula);
        }

        private final ConversionContext ctx;

        private FormulaRewriter(ConversionContext ctx) {
            this.ctx = ctx;
        }

        private Expr unexpected() {
            throw new AssertionError("unexpected node");
        }
       
        private Expr applyFormula(Expr expr) throws Err {
            if (!expr.type().is_bool) throw new AssertionError();
            return visitThis(expr);
        }

        @Override public Expr visit(ExprBinary x) throws Err {
            Pair<Expr, AndExpr> left = ExprRewriter.rewrite(ctx, x.left);
            Pair<Expr, AndExpr> right = ExprRewriter.rewrite(ctx, x.right);
            Expr newx = x.op.make(x.pos, x.closingBracket, left.a, right.a);
            AndExpr result = new AndExpr();
            result.add(left.b);
            result.add(right.b);
            result.add(newx);
            return result.getExpr();
        }
        @Override public Expr visit(ExprUnary x) throws Err {
            if (x.sub.type().is_bool)
                return x.op.make(x.pos, applyFormula(x.sub));
            else {
                Pair<Expr, AndExpr> rewritten = ExprRewriter.rewrite(ctx, x.sub);
                AndExpr result = new AndExpr();
                result.add(rewritten.b);
                result.add(x.op.make(x.pos, rewritten.a));
                return result.getExpr();
            }
        }
        @Override public Expr visit(ExprITE x) throws Err {
            return ExprITE.make(x.pos, applyFormula(x.cond), applyFormula(x.left), applyFormula(x.right));
        }
        @Override public Expr visit(ExprList x) throws Err {
            ConstList.TempList<Expr> args = new ConstList.TempList<Expr>();
            for (Expr e: x.args) {
                args.add(applyFormula(e));
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
            Pair<Expr, AndExpr> rewritten = ExprRewriter.rewrite(ctx, x.expr);
            AndExpr result = new AndExpr();
            result.add(rewritten.b);
            result.add(ExprLet.make(x.pos, x.var, rewritten.a, applyFormula(x.sub)));
            return result.getExpr();
        }
        @Override public Expr visit(Sig x) throws Err {
            return unexpected();
        }
        @Override public Expr visit(Sig.Field x) throws Err {
            return unexpected();
        }

        @Override public Expr visit(ExprCall x) throws Err {
            if (x.fun.label.equals("smtint/gt")) {
                return SintExprRewriter.rewriteFun(ctx, x, ">");
            } else if (x.fun.label.equals("smtint/eq")) {
                return SintExprRewriter.rewriteFun(ctx, x, "=");
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
            AndExpr result = new AndExpr();
            ConstList.TempList<Decl> decls = new ConstList.TempList<Decl>();
            for (Decl d : x.decls) {
                Pair<Expr, AndExpr> rewritten = ExprRewriter.rewrite(ctx, d.expr);
                Expr expr = rewritten.a;
                result.add(rewritten.b);
                ConstList.TempList<ExprHasName> names = new ConstList.TempList<ExprHasName>();
                for (ExprHasName ehn : d.names) {
                    ExprVar var = ExprVar.make(ehn.pos, ehn.label, expr.type());
                    names.add(var);
                }
                decls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, names.makeConst(), expr));
            }
            result.add(x.op.make(x.pos, x.closingBracket, decls.makeConst(), rewrite(ctx, x.sub)));
            return result.getExpr();
        }

    }


    private static class SintExprRewriter extends VisitReturn<ConstList<SExpr>> {

        public static Pair<Expr, AndExpr> rewrite(ConversionContext ctx, Expr expr) throws Err {
            SintExprRewriter rewriter = new SintExprRewriter(ctx);
            SExpr result = SExpr.and(rewriter.visitThis(expr).toArray(new SExpr[]{}));
            return new Pair<Expr, AndExpr>(ctx.makeRefSig(result).join(ctx.aqclass), rewriter.result);
        }

        public static Expr rewriteFun(ConversionContext ctx, ExprCall x, String smtOp) throws Err {
            SintExprRewriter rewriter = new SintExprRewriter(ctx);
            ConstList.TempList<ConstList<SExpr>> sexprs = new ConstList.TempList<ConstList<SExpr>>();
            for (Expr arg : x.args) {
                sexprs.add(rewriter.visitThis(arg));
            }
            rewriteFunRec(ctx, smtOp, sexprs.makeConst(), new SExpr[sexprs.size()], 0);
            return rewriter.result.getExpr();
        }

        private static void rewriteFunRec(ConversionContext ctx, String smtOp, ConstList<ConstList<SExpr>> sexprs, SExpr[] args, int depth) {
            if (depth == sexprs.size()) {
                ctx.addGlobalFact(SExpr.call(smtOp, args));
            } else {
                for (SExpr arg : sexprs.get(depth)) {
                    args[depth] = arg;
                    rewriteFunRec(ctx, smtOp, sexprs, args, depth + 1);
                }
            }
        }

        private final ConversionContext ctx;
        private final AndExpr result = new AndExpr();

        private SintExprRewriter(ConversionContext ctx) {
            this.ctx = ctx;
        }

        private ConstList<SExpr> unexpected() {
            throw new AssertionError("unexpected node");
        }

        @Override
        public ConstList<SExpr> visit(ExprCall x) throws Err {
            ConstList.TempList<SExpr> result = new ConstList.TempList<SExpr>();
            if (x.fun.label.equals("smtint/gt")) {
                for (SExpr left : visitThis(x.args.get(0))) {
                    for (SExpr right : visitThis(x.args.get(1))) {
                        result.add(SExpr.call(">", left, right));
                    }
                }
            } else if (x.fun.label.equals("smtint/plus")) {
                for (SExpr left : visitThis(x.args.get(0))) {
                    for (SExpr right : visitThis(x.args.get(1))) {
                        result.add(SExpr.call("+", left, right));
                    }
                }
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
                result.add(SExpr.num(c));
            } else {
                throw new AssertionError("User defined Sint functions not yet supported");
            }
            return result.makeConst();
        }

        @Override public ConstList<SExpr> visit(ExprBinary x) throws Err {
            // Relational expression in alloy which results in a Sint, e.g. a . (this/A <: v)
            Pair<Expr, AndExpr> left = ExprRewriter.rewrite(ctx, x.left);
            Pair<Expr, AndExpr> right = ExprRewriter.rewrite(ctx, x.right);
            Pair<ConstList<SExpr>, Expr> alias = ctx.makeAlias(x.op.make(x.pos, x.closingBracket, left.a, right.a));
            result.add(left.b);
            result.add(right.b);
            result.add(alias.b);
            return alias.a;
        }
        @Override public ConstList<SExpr> visit(ExprList x) throws Err {
            return unexpected();
        }
        @Override public ConstList<SExpr> visit(ExprConstant x) throws Err {
            return unexpected();
        }
        @Override public ConstList<SExpr> visit(ExprITE x) throws Err {
            return unexpected();
        }
        @Override public ConstList<SExpr> visit(ExprLet x) throws Err {
            return unexpected();
        }
        @Override public ConstList<SExpr> visit(ExprQt x) throws Err {
            return unexpected();
        }
        @Override public ConstList<SExpr> visit(ExprUnary x) throws Err {
            return unexpected();
        }
        @Override public ConstList<SExpr> visit(ExprVar x) throws Err {
            return unexpected();
        }
        @Override public ConstList<SExpr> visit(Sig x) throws Err {
            return unexpected();
        }
        @Override public ConstList<SExpr> visit(Sig.Field x) throws Err {
            return unexpected();
        }
    }

}
