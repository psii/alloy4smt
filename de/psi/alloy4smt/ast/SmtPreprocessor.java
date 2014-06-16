package de.psi.alloy4smt.ast;


import de.psi.alloy4smt.smt.SExpr;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstMap;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.*;

import java.util.*;

public class SmtPreprocessor {
    public static PreparedCommand build(Command c, ConstList<Sig> allReachableSigs) throws Err {
        ConversionInput input = new ConversionInput(c, allReachableSigs);
        FieldRewritePhase.Result frpr = FieldRewritePhase.run(input);
        FormulaRewritePhase.Result formr = FormulaRewritePhase.run(frpr);
        ComputeScopePhase.Result cspr = ComputeScopePhase.run(formr);
        return new PreparedCommand(c.change(cspr.scopes).change(formr.allsigs), frpr.sigSintref, null);
 /*
        FormulaRewritePhase ctx = new FormulaRewritePhase(c, allReachableSigs);
        for (Sig s : allReachableSigs) ctx.mapSig(s);
        Expr newformula = FormulaRewriter.rewrite(ctx, c.formula);
        return new PreparedCommand(
                c.change(ctx.getScopes()).change(ctx.getAdditionalFacts().and(newformula)),
                ctx.getAllSigs(), ctx.in.sigSintref, ctx.getSExprs());*/
    }

    private static class ConversionInput {
        public final Sig.PrimSig sigSint;
        public final Sig.PrimSig sigSintref;
        public final Sig.Field aqclass;
        public final ConstList<Sig> allReachableSigs;
        public final int defaultScope;
        public final Command command;

        ConversionInput(Command command, ConstList<Sig> allReachableSigs) {
            sigSint = (Sig.PrimSig) Helpers.getSigByName(allReachableSigs, "smtint/Sint");
            sigSintref = (Sig.PrimSig) Helpers.getSigByName(allReachableSigs, "smtint/SintRef");
            aqclass = Helpers.getFieldByName(sigSintref.getFields(), "aqclass");
            if (sigSint == null || sigSintref == null || aqclass == null)
                throw new AssertionError();
            this.allReachableSigs = allReachableSigs;
            defaultScope = command.overall < 0 ? 1 : command.overall;
            this.command = command;
        }
    }


    private static class FieldRewritePhase {
        public final Sig.PrimSig sigSint;
        public final Sig.PrimSig sigSintref;
        private final Map<Sig, Sig> newsigmap = new HashMap<Sig, Sig>();
        private final Map<Sig.Field, Sig.Field> newfieldmap = new HashMap<Sig.Field, Sig.Field>();
        private final ConstList.TempList<Sig> allsigs = new ConstList.TempList<Sig>();
        private final ConstList.TempList<FieldRewriter.Result> newrefs = new ConstList.TempList<FieldRewriter.Result>();

        public static class Result {
            public final Sig.PrimSig sigSint;
            public final Sig.PrimSig sigSintref;
            public final ConstList<Sig> allsigs;
            public final ConstList<FieldRewriter.Result> sigrefs;
            public final ConstMap<Sig, Sig> sigmap;
            public final ConstMap<Sig.Field, Sig.Field> fieldmap;
            public final ConversionInput input;

            private Result(Sig.PrimSig sigSint, Sig.PrimSig sigSintref, ConstList<Sig> allsigs, ConstList<FieldRewriter.Result> sigrefs, ConstMap<Sig, Sig> sigmap, ConstMap<Sig.Field, Sig.Field> fieldmap, ConversionInput input) {
                this.sigSint = sigSint;
                this.sigSintref = sigSintref;
                this.allsigs = allsigs;
                this.sigrefs = sigrefs;
                this.sigmap = sigmap;
                this.fieldmap = fieldmap;
                this.input = input;
            }
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
                            newrefs.add(rewriteResult);
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

        private FieldRewritePhase(ConversionInput in) throws Err {
            sigSint = in.sigSint;
            sigSintref = in.sigSintref;
            addSigMapping(in.sigSintref, in.sigSintref);
            for (Sig.Field f : in.sigSintref.getFields())
                newfieldmap.put(f, f);
            for (Sig s : in.allReachableSigs)
                mapSig(s);
        }

        public static Result run(ConversionInput in) throws Err {
            FieldRewritePhase p = new FieldRewritePhase(in);
            return new Result(p.sigSint, p.sigSintref, p.allsigs.makeConst(), p.newrefs.makeConst(), ConstMap.make(p.newsigmap), ConstMap.make(p.newfieldmap), in);
        }
    }

    private static class FieldRewriter extends VisitReturn<Expr> {
        private final FieldRewritePhase ctx;
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

        public static Result rewrite(FieldRewritePhase ctx, Sig sig, Sig.Field field) throws Err {
            FieldRewriter rewriter = new FieldRewriter(ctx, sig, field);
            Expr expr = rewriter.visitThis(field.decl().expr);
            return new Result(rewriter.ref, expr, rewriter.visitedsigs.makeConst());
        }

        private FieldRewriter(FieldRewritePhase ctx, Sig sig, Sig.Field field) {
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


    private static class FormulaRewritePhase {
        public final FieldRewritePhase.Result in;
        public final Sig.Field aqclass;
        private final ConstList.TempList<SintExprDef> sintExprDefs = new ConstList.TempList<SintExprDef>();
        private final ConstList.TempList<Sig> allsigs;
        private final ConstList.TempList<SExpr<Sig>> sexprs = new ConstList.TempList<SExpr<Sig>>();

        private int exprcnt = 0;

        public static class SintExprDef {
            public final Sig.PrimSig sig;
            public final Iterable<Type> dependencies;

            public SintExprDef(Sig.PrimSig sig, Iterable<Type> dependencies) {
                this.sig = sig;
                this.dependencies = dependencies;
            }
        }

        public static class Result {
            public final ConstList<SintExprDef> sintExprDefs;
            public final ConstList<Sig> allsigs;
            public final ConstList<SExpr<Sig>> sexprs;
            public final Expr newformula;
            public final FieldRewritePhase.Result frp;

            public Result(ConstList<SintExprDef> sintExprDefs, ConstList<Sig> allsigs, ConstList<SExpr<Sig>> sexprs, Expr newformula, FieldRewritePhase.Result frp) {
                this.sintExprDefs = sintExprDefs;
                this.allsigs = allsigs;
                this.sexprs = sexprs;
                this.newformula = newformula;
                this.frp = frp;
            }
        }

        private FormulaRewritePhase(FieldRewritePhase.Result in) {
            this.in = in;
            this.aqclass = in.input.aqclass;
            this.allsigs = new ConstList.TempList<Sig>(in.allsigs);
        }

        public static Result run(FieldRewritePhase.Result in) throws Err {
            FormulaRewritePhase p = new FormulaRewritePhase(in);
            Expr expr = FormulaRewriter.rewrite(p, in.input.command.formula);
            return new Result(p.sintExprDefs.makeConst(), p.allsigs.makeConst(), p.sexprs.makeConst(), expr, in);
        }

        public Sig mapSig(Sig old) throws Err {
            Sig res = in.sigmap.get(old);
            if (res == null) throw new AssertionError();
            return res;
        }

        public Sig.Field mapField(Sig.Field old) {
            Sig.Field field = in.fieldmap.get(old);
            if (field == null) throw new AssertionError();
            return field;
        }

        public void addRefSig(Sig.PrimSig ref, Iterable<Type> dependencies) throws Err {
            allsigs.add(ref);
            sintExprDefs.add(new SintExprDef(ref, dependencies));
        }

        public void addGlobalFact(SExpr<Sig> sexpr) {
            sexprs.add(sexpr);
        }

        public Expr makeRefSig(SExpr<Sig> sexpr) throws Err {
            StringBuilder sb = new StringBuilder();
            sb.append("SintExpr");
            sb.append(exprcnt++);
            Sig.PrimSig ref = new Sig.PrimSig(sb.toString(), in.sigSintref);
            addRefSig(ref, new Vector<Type>());
            SExpr<Sig> symb = SExpr.<Sig>sym(sb.toString() + "$0");
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
        public Pair<SExpr<Sig>, Expr> makeAlias(Expr expr) throws Err {
            if (!isSintRefExpr(expr)) throw new AssertionError();
            final Set<ExprVar> usedquantifiers = FreeVarFinder.find(expr);
            final List<Type> dependencies = new Vector<Type>();

            exprcnt++;
            Sig.PrimSig ref = new Sig.PrimSig("SintExpr" + exprcnt, in.sigSintref);

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
            addRefSig(ref, dependencies);
            SExpr<Sig> var = SExpr.<Sig>leaf(ref);
            return new Pair<SExpr<Sig>, Expr>(var, left.join(aqclass).equal(expr.join(aqclass)));
        }

        public boolean isSintRefExpr(Expr expr) {
            return expr.type().isSubtypeOf(in.sigSintref.type());
        }

        public boolean isSintExpr(Expr expr) {
            return expr.type().equals(in.sigSint.type());
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




    private static class ExprRewriter extends VisitReturn<Expr> {

        public static Pair<Expr, AndExpr> rewrite(FormulaRewritePhase ctx, Expr expr) throws Err {
            ExprRewriter rewriter = new ExprRewriter(ctx);
            return new Pair<Expr, AndExpr>(rewriter.apply(expr), rewriter.result);
        }

        private final FormulaRewritePhase ctx;
        private final AndExpr result = new AndExpr();

        private ExprRewriter(FormulaRewritePhase ctx) {
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

        public static Expr rewrite(FormulaRewritePhase ctx, Expr formula) throws Err {
            if (!formula.type().is_bool) throw new AssertionError();
            FormulaRewriter rewriter = new FormulaRewriter(ctx);
            // We don't use `applyFormula` here, because FormulaRewriter is also used by
            // SintExprRewriter to rewrite subexpressions.
            return rewriter.visitThis(formula);
        }

        private final FormulaRewritePhase ctx;

        private FormulaRewriter(FormulaRewritePhase ctx) {
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


    private static class SintExprRewriter extends VisitReturn<SExpr<Sig>> {

        public static Pair<Expr, AndExpr> rewrite(FormulaRewritePhase ctx, Expr expr) throws Err {
            SintExprRewriter rewriter = new SintExprRewriter(ctx);
            SExpr<Sig> result = rewriter.visitThis(expr);
            return new Pair<Expr, AndExpr>(ctx.makeRefSig(result).join(ctx.aqclass), rewriter.result);
        }

        public static Expr rewriteFun(FormulaRewritePhase ctx, ExprCall x, String smtOp) throws Err {
            SintExprRewriter rewriter = new SintExprRewriter(ctx);
            ConstList.TempList<SExpr<Sig>> sexprs = new ConstList.TempList<SExpr<Sig>>();
            sexprs.add(SExpr.<Sig>sym(smtOp));
            for (Expr arg : x.args) {
                sexprs.add(rewriter.visitThis(arg));
            }
            ctx.addGlobalFact(new SExpr.SList<Sig>(sexprs.makeConst()));
            return rewriter.result.getExpr();
        }

        private final FormulaRewritePhase ctx;
        private final AndExpr result = new AndExpr();

        private SintExprRewriter(FormulaRewritePhase ctx) {
            this.ctx = ctx;
        }

        private SExpr<Sig> unexpected() {
            throw new AssertionError("unexpected node");
        }

        @Override
        public SExpr<Sig> visit(ExprCall x) throws Err {
            SExpr<Sig> result;
            if (x.fun.label.equals("smtint/gt")) {
                result = SExpr.<Sig>call(">", visitThis(x.args.get(0)), visitThis(x.args.get(1)));
            } else if (x.fun.label.equals("smtint/plus")) {
                result = SExpr.<Sig>call("+", visitThis(x.args.get(0)), visitThis(x.args.get(1)));
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
                result = SExpr.<Sig>num(c);
            } else {
                throw new AssertionError("User defined Sint functions not yet supported");
            }
            return result;
        }

        @Override public SExpr<Sig> visit(ExprBinary x) throws Err {
            // Relational expression in alloy which results in a Sint, e.g. a . (this/A <: v)
            Pair<Expr, AndExpr> left = ExprRewriter.rewrite(ctx, x.left);
            Pair<Expr, AndExpr> right = ExprRewriter.rewrite(ctx, x.right);
            Pair<SExpr<Sig>, Expr> alias = ctx.makeAlias(x.op.make(x.pos, x.closingBracket, left.a, right.a));
            result.add(left.b);
            result.add(right.b);
            result.add(alias.b);
            return alias.a;
        }
        @Override public SExpr<Sig> visit(ExprList x) throws Err {
            return unexpected();
        }
        @Override public SExpr<Sig> visit(ExprConstant x) throws Err {
            return unexpected();
        }
        @Override public SExpr<Sig> visit(ExprITE x) throws Err {
            return unexpected();
        }
        @Override public SExpr<Sig> visit(ExprLet x) throws Err {
            return unexpected();
        }
        @Override public SExpr<Sig> visit(ExprQt x) throws Err {
            return unexpected();
        }
        @Override public SExpr<Sig> visit(ExprUnary x) throws Err {
            return unexpected();
        }
        @Override public SExpr<Sig> visit(ExprVar x) throws Err {
            return unexpected();
        }
        @Override public SExpr<Sig> visit(Sig x) throws Err {
            return unexpected();
        }
        @Override public SExpr<Sig> visit(Sig.Field x) throws Err {
            return unexpected();
        }
    }



    private static class ComputeScopePhase {
        private final ConstList.TempList<CommandScope> scopes = new ConstList.TempList<CommandScope>();

        public static class Result {
            public final ConstList<CommandScope> scopes;

            public Result(ConstList<CommandScope> scopes) {
                this.scopes = scopes;
            }
        }

        private ComputeScopePhase(FormulaRewritePhase.Result in) {

        }

        public static Result run(FormulaRewritePhase.Result in) {
            ComputeScopePhase p = new ComputeScopePhase(in);
            return new Result(p.scopes.makeConst());
        }
    }
}
