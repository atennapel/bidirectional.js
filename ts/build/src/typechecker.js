"use strict";
exports.__esModule = true;
var Result_1 = require("./Result");
var types_1 = require("./types");
var exprs_1 = require("./exprs");
var context_1 = require("./context");
var ok = function (t) { return Result_1.Result.ok(t); };
var err = function (m) { return Result_1.Result.err(new TypeError(m)); };
var InferState = (function () {
    function InferState(current, currentVar) {
        this.current = current;
        this.currentVar = currentVar;
    }
    InferState.empty = function () { return new InferState(types_1.TypeId.first(), 0); };
    InferState.prototype.fresh = function () {
        return [new InferState(this.current.next(), this.currentVar), this.current];
    };
    InferState.prototype.freshVar = function () {
        return [new InferState(this.current, this.currentVar + 1), "$" + this.currentVar];
    };
    return InferState;
}());
exports.InferState = InferState;
var subtype = function (state, context, t1, t2) {
    if (!context.isWellformed())
        return err("Ill-formed context in subtype: " + context);
    if (!t1.isWellformed(context))
        return err("Ill-formed type in subtype: " + t1 + " with " + context);
    if (!t2.isWellformed(context))
        return err("Ill-formed type in subtype: " + t2 + " with " + context);
    if (t1 instanceof types_1.TVar && t2 instanceof types_1.TVar && t1.id.equals(t2.id))
        return ok([state, context]);
    if (t1 instanceof types_1.TExists && t2 instanceof types_1.TExists && t1.id.equals(t2.id))
        return ok([state, context]);
    if (t1 instanceof types_1.TUnit && t2 instanceof types_1.TUnit)
        return ok([state, context]);
    if (t1 instanceof types_1.TFun && t2 instanceof types_1.TFun)
        return subtype(state, context, t2.left, t1.left)
            .then(function (_a) {
            var st1 = _a[0], c1 = _a[1];
            return subtype(st1, c1, t1.right.apply(c1), t2.right.apply(c1));
        });
    if (t1 instanceof types_1.TForall) {
        var _a = state.fresh(), st1 = _a[0], id_1 = _a[1];
        return subtype(st1, context.add(context_1.cmarker(id_1), context_1.cexists(id_1)), t1.type.subst(t1.tvar, types_1.texists(id_1)), t2).then(function (_a) {
            var st2 = _a[0], c1 = _a[1];
            return ok([st2, c1.dropFrom(context_1.cmarker(id_1))]);
        });
    }
    if (t2 instanceof types_1.TForall)
        return subtype(state, context.add(context_1.cforall(t2.tvar)), t1, t2.type).then(function (_a) {
            var st1 = _a[0], c1 = _a[1];
            return ok([st1, c1.dropFrom(context_1.cforall(t2.tvar))]);
        });
    if (t1 instanceof types_1.TExists && !t2.free().contains(t1.id))
        return instantiateL(state, context, t1.id, t2);
    if (t2 instanceof types_1.TExists && !t1.free().contains(t2.id))
        return instantiateR(state, context, t1, t2.id);
    return err('Subtype failed on ' + t1 + ' and ' + t2 + ' with ' + context);
};
var solve = function (context, tvar, type) {
    if (!type.isMono())
        return err("Cannot solve with a polytype: " + tvar + " = " + type);
    var _a = context.split(context_1.cexists(tvar)), left = _a[0], right = _a[1];
    if (type.isWellformed(left))
        return ok(context_1.Context.join(left, context_1.cexistssolved(tvar, type), right));
    return err("Ill-formed type in solve: " + type);
};
var instantiateL = function (state, context, tv, type) {
    if (!context.isWellformed())
        return err("Ill-formed context in instantiateL: " + context);
    if (!types_1.texists(tv).isWellformed(context))
        return err("Ill-formed type in instantiateL: " + types_1.texists(tv) + " with " + context);
    if (!type.isWellformed(context))
        return err("Ill-formed type in instantiateL: " + type + " with " + context);
    return solve(context, tv, type)
        .then(function (c) { return ok([state, c]); })
        .onErr(function (_) {
        if (type instanceof types_1.TExists)
            return context.isOrdered(tv, type.id) ?
                solve(context, type.id, types_1.texists(tv)).map(function (c) { return [state, c]; }) :
                solve(context, tv, types_1.texists(type.id)).map(function (c) { return [state, c]; });
        if (type instanceof types_1.TFun) {
            var _a = state.fresh(), st1 = _a[0], alpha1 = _a[1];
            var _b = st1.fresh(), st2 = _b[0], alpha2_1 = _b[1];
            return instantiateR(st2, context.insertAt(context_1.cexists(tv), [
                context_1.cexists(alpha2_1),
                context_1.cexists(alpha1),
                context_1.cexistssolved(tv, types_1.tfun(types_1.texists(alpha1), types_1.texists(alpha2_1))),
            ]), type.left, alpha1).then(function (_a) {
                var st3 = _a[0], c1 = _a[1];
                return instantiateL(st3, c1, alpha2_1, type.right.apply(c1));
            });
        }
        if (type instanceof types_1.TForall) {
            var _c = state.fresh(), st1 = _c[0], beta_1 = _c[1];
            return instantiateL(st1, context.add(context_1.cforall(beta_1)), tv, type.type.subst(type.tvar, types_1.tvar(beta_1))).map(function (_a) {
                var st2 = _a[0], c1 = _a[1];
                return [st2, c1.dropFrom(context_1.cforall(beta_1))];
            });
        }
        return err("instantiateL failed: " + context);
    });
};
var instantiateR = function (state, context, type, tv) {
    if (!context.isWellformed())
        return err("Ill-formed context in instantiateR: " + context);
    if (!type.isWellformed(context))
        return err("Ill-formed type in instantiateR: " + type + " with " + context);
    if (!types_1.texists(tv).isWellformed(context))
        return err("Ill-formed type in instantiateR: " + types_1.texists(tv) + " with " + context);
    return solve(context, tv, type)
        .then(function (c) { return ok([state, c]); })
        .onErr(function (_) {
        if (type instanceof types_1.TExists)
            return context.isOrdered(tv, type.id) ?
                solve(context, type.id, types_1.texists(tv)).map(function (c) { return [state, c]; }) :
                solve(context, tv, types_1.texists(type.id)).map(function (c) { return [state, c]; });
        if (type instanceof types_1.TFun) {
            var _a = state.fresh(), st1 = _a[0], alpha1 = _a[1];
            var _b = st1.fresh(), st2 = _b[0], alpha2_2 = _b[1];
            return instantiateL(st2, context.insertAt(context_1.cexists(tv), [
                context_1.cexists(alpha2_2),
                context_1.cexists(alpha1),
                context_1.cexistssolved(tv, types_1.tfun(types_1.texists(alpha1), types_1.texists(alpha2_2))),
            ]), alpha1, type.left).then(function (_a) {
                var st3 = _a[0], c1 = _a[1];
                return instantiateR(st3, c1, type.right.apply(c1), alpha2_2);
            });
        }
        if (type instanceof types_1.TForall) {
            var _c = state.fresh(), st1 = _c[0], beta_2 = _c[1];
            return instantiateR(st1, context.add(context_1.cmarker(beta_2), context_1.cexists(beta_2)), type.type.subst(type.tvar, types_1.texists(beta_2)), tv).map(function (_a) {
                var st2 = _a[0], c1 = _a[1];
                return [st2, c1.dropFrom(context_1.cmarker(beta_2))];
            });
        }
        return err("instantiateL failed: " + context);
    });
};
var typecheck = function (state, context, expr, type) {
    // console.log(`typecheck ${expr} ${type} ${context}`);
    if (!context.isWellformed())
        return err("Ill-formed context in typecheck: " + context);
    if (!type.isWellformed(context))
        return err("Ill-formed type in typecheck: " + type + " with " + context);
    if (expr instanceof exprs_1.EUnit && type instanceof types_1.TUnit)
        return ok([state, context]);
    if (type instanceof types_1.TForall) {
        var _a = state.fresh(), st1 = _a[0], tv_1 = _a[1];
        return typecheck(st1, context.add(context_1.cforall(tv_1)), expr, type.type.subst(type.tvar, types_1.tvar(tv_1))).map(function (_a) {
            var st1 = _a[0], c = _a[1];
            return [st1, c.dropFrom(context_1.cforall(tv_1))];
        });
    }
    if (expr instanceof exprs_1.ELam && type instanceof types_1.TFun) {
        var _b = state.freshVar(), st1 = _b[0], x_1 = _b[1];
        return typecheck(st1, context.add(context_1.cvar(x_1, type.left)), expr.body.subst(expr.arg, exprs_1.evar(x_1)), type.right).map(function (_a) {
            var st2 = _a[0], c = _a[1];
            return [st2, c.dropFrom(context_1.cvar(x_1, type.left))];
        });
    }
    return typesynth(state, context, expr)
        .then(function (_a) {
        var st1 = _a[0], t = _a[1], c = _a[2];
        return subtype(st1, c, t.apply(c), type.apply(c));
    });
};
var typesynth = function (state, context, expr) {
    // console.log(`typesynth ${expr} ${context}`);
    if (!context.isWellformed())
        return err("Ill-formed context in typesynth: " + context);
    if (expr instanceof exprs_1.EVar) {
        var type = context.getType(expr.name);
        if (!type)
            return err("Not in scope: " + expr.name);
        return ok([state, type, context]);
    }
    if (expr instanceof exprs_1.EAnno)
        return typecheck(state, context, expr.expr, expr.type)
            .map(function (_a) {
            var st1 = _a[0], c = _a[1];
            return [st1, expr.type, c];
        });
    if (expr instanceof exprs_1.EApp)
        return typesynth(state, context, expr.left)
            .then(function (_a) {
            var st1 = _a[0], t = _a[1], c = _a[2];
            return typeapplysynth(st1, c, t.apply(c), expr.right);
        });
    if (expr instanceof exprs_1.ELam) {
        var _a = state.freshVar(), st1 = _a[0], x = _a[1];
        var _b = st1.fresh(), st2 = _b[0], alpha_1 = _b[1];
        var _c = st2.fresh(), st3 = _c[0], beta_3 = _c[1];
        return typecheck(st3, context.add(context_1.cexists(alpha_1), context_1.cexists(beta_3), context_1.cvar(x, types_1.texists(alpha_1))), expr.body.subst(expr.arg, exprs_1.evar(x)), types_1.texists(beta_3)).map(function (_a) {
            var st = _a[0], c = _a[1];
            return [st, types_1.tfun(types_1.texists(alpha_1), types_1.texists(beta_3)), c];
        });
    }
    if (expr instanceof exprs_1.EUnit)
        return ok([state, types_1.tunit, context]);
    return err("typesynth failed for " + expr);
};
var typeapplysynth = function (state, context, type, expr) {
    // console.log(`typeapplysynth ${type} ${expr} ${context}`);
    if (!context.isWellformed())
        return err("Ill-formed context in typeapplysynth: " + context);
    if (!type.isWellformed(context))
        return err("Ill-formed type in typeapplysynth: " + type + " with " + context);
    if (type instanceof types_1.TForall) {
        var _a = state.fresh(), st1 = _a[0], alpha = _a[1];
        return typeapplysynth(st1, context.add(context_1.cexists(alpha)), type.type.subst(type.tvar, types_1.texists(alpha)), expr);
    }
    if (type instanceof types_1.TExists) {
        var _b = state.fresh(), st1 = _b[0], alpha1 = _b[1];
        var _c = st1.fresh(), st2 = _c[0], alpha2_3 = _c[1];
        return typecheck(st2, context.insertAt(context_1.cexists(type.id), [
            context_1.cexists(alpha2_3),
            context_1.cexists(alpha1),
            context_1.cexistssolved(type.id, types_1.tfun(types_1.texists(alpha1), types_1.texists(alpha2_3)))
        ]), expr, types_1.texists(alpha1)).map(function (_a) {
            var st = _a[0], c = _a[1];
            return [st, types_1.texists(alpha2_3), c];
        });
    }
    if (type instanceof types_1.TFun)
        return typecheck(state, context, expr, type.left)
            .map(function (_a) {
            var st = _a[0], c = _a[1];
            return [st, type.right, c];
        });
    return err("typeapplysynth failed for " + type + " and " + expr);
};
exports.infer = function (expr, context_, state_) {
    var context = context_ || context_1.Context.empty();
    var state = state_ || InferState.empty();
    return typesynth(state, context, expr)
        .map(function (_a) {
        var _ = _a[0], t = _a[1], c = _a[2];
        return t.apply(c);
    });
};
