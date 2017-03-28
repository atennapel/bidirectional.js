/* TODO:
 *  tvars/vars with names instead of numbers
 *  newtypes/pack/unpack
 *  literals (ints/floats/string/bool)
 *  row polymorphism
 *  typeclasses
 */
var E = require('./exprs');
var K = require('./kinds');
var T = require('./types');
var C = require('./context');

// Context
var contains = (v, a) => a.indexOf(v) >= 0;

var wf = c => {
  if(c.length === 0) return true;
  var rest = c.slice(1);
  if(!wf(rest)) return false;
  var e = c[0];
  if(e.tag === C.CForall) return !contains(e.name, C.foralls(rest));
  if(e.tag === C.CVar)
    return !contains(e.name, C.vars(rest)) && typewf(rest, e.type);
  if(e.tag === C.CExists)
    return !contains(e.name, C.existentials(rest));
  if(e.tag === C.CExistsSolved)
    return !contains(e.name, C.existentials(rest)) && typewf(rest, e.type);
  if(e.tag === C.CMarker)
    return !contains(e.name, C.markers(rest)) &&
      !contains(e.name, C.existentials(rest));
  throw new Error('Invalid element in Context: ' + e);
};

var typewf = (c, t) => {
  if(t.tag === T.TVar) return contains(t.name, C.foralls(c));
  if(t.tag === T.TCon) return true;
  if(t.tag === T.TFun) return typewf(c, t.left) && typewf(c, t.right);
  if(t.tag === T.TApp) return typewf(c, t.left) && typewf(c, t.right);
  if(t.tag === T.TForall)
    return typewf(C.snoc(c, C.cforall(t.arg.name, t.arg.kind)), t.type);
  if(t.tag === T.TExists) return contains(t.name, C.existentials(c));
  throw new Error('Invalid type in typewf: ' + t);
};

var checkwf = c => {
  if(!wf(c)) throw new Error('Malformed context ' + C.contextStr(c));
};

var checktypewf = (c, t) => {
  if(!typewf(c, t)) throw new Error('Malformed type ' + T.str(t));
  checkwf(c);
};

var findSolved = (c, v) => {
  var x = c.find(x => x.tag === C.CExistsSolved && x.name === v);
  return x? x.type: null;
};

var findVarType = (c, v) => {
  var x = c.find(x => x.tag === C.CVar && x.name === v);
  return x? x.type: null;
};

var solve = (c, v, t) => {
  var broken = C.breakMarker(C.cexists(v), c);
  var gammaL = broken[0];
  var gammaR = broken[1];
  if(typewf(gammaL, t))
    return C.append(C.appendElems(gammaL, [C.cexistssolved(v, t)]), gammaR);
  return null;
};

var apply = (gamma, t) => {
  if(t.tag === T.TCon) return t;
  if(t.tag === T.TVar) return t;
  if(t.tag === T.TForall) return T.tforall(t.arg, apply(gamma, t.type));
  if(t.tag === T.TExists) {
    var solved = findSolved(gamma, t.name);
    if(!solved) return t;
    return apply(gamma, solved);
  }
  if(t.tag === T.TFun)
    return T.tfun(apply(gamma, t.left), apply(gamma, t.right));
  if(t.tag === T.TApp)
    return T.tapp(apply(gamma, t.left), apply(gamma, t.right));
  throw new Error('Invalid type in apply: ' + t);
};

var ordered = (gamma, alpha, beta) =>
  contains(alpha, C.existentials(C.dropMarker(C.cexists(beta), gamma)));

// NameGen
var clone = function(o) {
  var n = {};
  for(var k in o) n[k] = o[k];
  for(var i = 1, l = arguments.length; i < l; i += 2)
    n[arguments[i]] = arguments[i + 1];
  return n;
};

var initialState = {
  var: 0,
  tvar: 0,
};

var freshVar = state => ({
  var: '$' + state.var,
  state: clone(state, 'var', state.var + 1),
});
var freshTVar = state => ({
  tvar: "'" + state.tvar,
  state: clone(state, 'tvar', state.tvar + 1),
});
var freshTVars = (state, n) => {
  var r = [];
  for(var i = 0; i < n; i++) r.push("'" + (state.tvar + i));
  return {
    tvars: r,
    state: clone(state, 'tvar', state.tvar + n),
  }
};

// Type
var subtype = (state, gamma, t1, t2) => {
  // console.log('subtype ' + C.contextStr(gamma) + ' ' + T.str(t1) + ' ' + T.str(t2));
  checktypewf(gamma, t1);
  checktypewf(gamma, t2);
  if(!K.eq(t1.kind, t2.kind))
    throw new Error('kind mismatch: ' + T.str(t1) + ' and ' + T.str(t2));
  if(t1.tag === T.TVar && t2.tag === T.TVar && t1.name === t2.name)
    return { state, context: gamma };
  if(t1.tag === T.TCon && t2.tag === T.TCon && t1.name === t2.name)
    return { state, context: gamma };
  if(t1.tag === T.TExists && t2.tag === T.TExists
    && t1.name === t2.name
    && contains(t1.name, C.existentials(gamma)))
    return { state, context: gamma };
  if(t1.tag === T.TApp && t2.tag === T.TApp) {
    var r = subtype(state, gamma, t1.left, t2.left);
    return subtype(
      r.state,
      r.context,
      apply(r.context, t1.right),
      apply(r.context, t2.right)
    );
  }
  if(t1.tag === T.TFun && t2.tag === T.TFun) {
    var r = subtype(state, gamma, t2.left, t1.left);
    return subtype(
      r.state,
      r.context,
      apply(r.context, t1.right),
      apply(r.context, t2.right)
    );
  }
  if(t2.tag === T.TForall) {
    var r1 = freshTVar(state);
    var v = r1.tvar;
    var vkind = t2.arg.kind;
    var r2 = subtype(
      r1.state,
      C.snoc(gamma, C.cforall(v, vkind)),
      t1,
      T.subst(T.tvar(v, vkind), t2.arg.name, t2.type)
    );
    return {
      state: r2.state,
      context: C.dropMarker(C.cforall(v, vkind), r2.context),
    };
  }
  if(t1.tag === T.TForall) {
    var r1 = freshTVar(state);
    var v = r1.tvar;
    var vkind = t1.arg.kind;
    var r2 = subtype(
      r1.state,
      C.appendElems(gamma, [C.cmarker(v), C.cexists(v, vkind)]),
      T.subst(T.texists(v, vkind), t1.arg.name, t1.type),
      t2
    );
    return {
      state: r2.state,
      context: C.dropMarker(C.cmarker(v), r2.context),
    };
  }
  if(t1.tag === T.TExists
    && contains(t1.name, C.existentials(gamma))
    && !contains(t1.name, T.freeTVars(t2))) {
    return instantiateL(state, gamma, t1.name, t2);
  }
  if(t2.tag === T.TExists
    && contains(t2.name, C.existentials(gamma))
    && !contains(t2.name, T.freeTVars(t1))) {
    return instantiateR(state, gamma, t1, t2.name);
  }
  throw new Error('subtype failed: ' + T.str(t1) + ' and ' + T.str(t2));
};

var instantiateL = (state, gamma, alpha, a) => {
  // console.log('instantiateL ' + C.contextStr(gamma) + ' ' + alpha + ' ' + T.str(a));
  checktypewf(gamma, a);
  checktypewf(gamma, T.texists(alpha));
  var gamma_ = T.isMonotype(a)? solve(gamma, alpha, a): null;
  if(gamma_) return { state, context: gamma_ };
  if(a.tag === T.TExists) {
    if(ordered(gamma, alpha, a.name)) {
      var solved = solve(gamma, a.name, T.texists(alpha));
      if(!solved) throw new Error('instantiateL failed');
      return { state, context: solved };
    } else {
      var solved = solve(gamma, alpha, T.texists(a.name));
      if(!solved) throw new Error('instantiateL failed');
      return { state, context: solved };
    }
  }
  if(a.tag === T.TFun) {
    var r1 = freshTVar(state);
    var alpha1 = r1.tvar;
    var r2 = freshTVar(r1.state);
    var alpha2 = r2.tvar;
    var r3 = instantiateR(
      r2.state,
      C.insertAt(gamma, C.cexists(alpha), C.context([
        C.cexists(alpha2),
        C.cexists(alpha1),
        C.cexistssolved(alpha, T.tfun(T.texists(alpha1), T.texists(alpha2))),
      ])),
      a.left,
      alpha1
    );
    return instantiateL(
      r3.state,
      r3.context,
      alpha2,
      apply(r3.context, a.right)
    );
  }
  if(a.tag === T.TApp) {
    var r1 = freshTVar(state);
    var alpha1 = r1.tvar;
    var r2 = freshTVar(r1.state);
    var alpha2 = r2.tvar;
    var r3 = instantiateR(
      r2.state,
      insertAt(gamma, C.cexists(alpha), C.context([
        C.cexists(alpha2),
        C.cexists(alpha1),
        C.cexistssolved(alpha, T.tapp(T.texists(alpha1), T.texists(alpha2))),
      ])),
      a.left,
      alpha1
    );
    return instantiateL(
      r3.state,
      r3.context,
      alpha2,
      apply(r3.context, a.right)
    );
  }
  if(a.tag === T.TForall) {
    var r1 = freshTVar(state);
    var beta_ = r1.tvar;
    var vkind = a.arg.kind;
    var r2 = instantiateL(
      r1.state,
      C.appendElems(gamma, [C.cforall(beta_, vkind)]),
      alpha,
      T.subst(T.tvar(beta_, vkind), a.arg.name, a.type)
    );
    return {
      state: r2.state,
      context: C.dropMarker(C.cforall(beta_, vkind), r2.context),
    };
  }
  throw new Error('instantiateL failed');
};

var instantiateR = (state, gamma, a, alpha) => {
  // console.log('instantiateR ' + C.contextStr(gamma) + ' ' + T.str(a) + ' ' + alpha);
  checktypewf(gamma, a);
  checktypewf(gamma, T.texists(alpha));
  var gamma_ = T.isMonotype(a)? solve(gamma, alpha, a): null;
  if(gamma_) return { state, context: gamma_ };
  if(a.tag === T.TExists) {
    if(ordered(gamma, alpha, a.name)) {
      var solved = solve(gamma, a.name, T.texists(alpha));
      if(!solved) throw new Error('instantiateR failed');
      return { state, context: solved };
    } else {
      var solved = solve(gamma, alpha, T.texists(a.name));
      if(!solved) throw new Error('instantiateR failed');
      return { state, context: solved };
    }
  }
  if(a.tag === T.TFun) {
    var r1 = freshTVar(state);
    var alpha1 = r1.tvar;
    var r2 = freshTVar(r1.state);
    var alpha2 = r2.tvar;
    var r3 = instantiateL(
      r2.state,
      C.insertAt(gamma, C.cexists(alpha), C.context([
        C.cexists(alpha2),
        C.cexists(alpha1),
        C.cexistssolved(alpha, T.tfun(T.texists(alpha1), T.texists(alpha2))),
      ])),
      alpha1,
      a.left
    );
    return instantiateR(
      r3.state,
      r3.context,
      apply(r3.context, a.right),
      alpha2
    );
  }
  if(a.tag === T.TApp) {
    var r1 = freshTVar(state);
    var alpha1 = r1.tvar;
    var r2 = freshTVar(r1.state);
    var alpha2 = r2.tvar;
    var r3 = instantiateL(
      r2.state,
      C.insertAt(gamma, C.cexists(alpha), C.context([
        C.cexists(alpha2),
        C.cexists(alpha1),
        C.cexistssolved(alpha, T.tapp(T.texists(alpha1), T.texists(alpha2))),
      ])),
      alpha1,
      a.left
    );
    return instantiateR(
      r3.state,
      r3.context,
      apply(r3.context, a.right),
      alpha2
    );
  }
  if(a.tag === T.TForall) {
    var r1 = freshTVar(state);
    var beta_ = r1.tvar;
    var vkind = a.arg.kind;
    var r2 = instantiateR(
      r1.state,
      C.appendElems(gamma, [C.cmarker(beta_), C.cexists(beta_, vkind)]),
      T.subst(T.texists(beta_, vkind), a.arg.name, a.type),
      alpha
    );
    return {
      state: r2.state,
      context: C.dropMarker(C.cmarker(beta_), r2.context),
    };
  }
  throw new Error('instantiateR failed');
};

var typecheck = (state, gamma, expr, type) => {
  // console.log('typecheck', C.contextStr(gamma), E.str(expr), T.str(type));
  checktypewf(gamma, type);
  if(expr.tag === E.EUnit && type === T.tunit)
    return { state, context: gamma };
  if(type.tag === T.TForall) {
    var r1 = freshTVar(state);
    var alpha_ = r1.tvar;
    var vkind = type.arg.kind;
    var r2 = typecheck(
      r1.state,
      C.snoc(gamma, C.cforall(alpha_, vkind)),
      expr,
      T.subst(T.tvar(alpha_, vkind), type.arg.name, type.type)
    );
    return {
      state: r2.state,
      context: C.dropMarker(C.cforall(alpha_, vkind), r2.context),
    };
  }
  if(expr.tag === E.EAbs && type.tag === T.TFun) {
    var r1 = freshVar(state);
    var x_ = r1.var;
    var r2 = typecheck(
      r1.state,
      C.snoc(gamma, C.cvar(x_, type.left)),
      E.subst(E.evar(x_), expr.arg, expr.body),
      type.right
    );
    return {
      state: r2.state,
      context: C.dropMarker(C.cvar(x_, type.left), r2.context),
    };
  }
  var r1 = typesynth(state, gamma, expr);
  return subtype(
    r1.state,
    r1.context,
    apply(r1.context, r1.type),
    apply(r1.context, type)
  );
};

var typesynth = (state, gamma, expr) => {
  // console.log('typesynth', C.contextStr(gamma), E.str(expr));
  checkwf(gamma);
  if(expr.tag === E.EVar) {
    var type = findVarType(gamma, expr.name);
    if(!type) throw new Error('Not in scope ' + expr.name);
    return {
      state,
      context: gamma,
      type,
    };
  }
  if(expr.tag === E.EAnno) {
    var r = typecheck(state, gamma, expr.expr, expr.type);
    return {
      state: r.state,
      context: r.context,
      type: expr.type,
    };
  }
  if(expr.tag === E.EUnit)
    return { state, context: gamma, type: T.tunit };
  if(expr.tag === E.EAbs) {
    var r1 = freshVar(state);
    var x_ = r1.var;
    var r2 = freshTVar(r1.state);
    var alpha = r2.tvar;
    var r3 = freshTVar(r2.state);
    var beta = r3.tvar;
    var r4 = typecheck(
      r3.state,
      C.appendElems(gamma, [
        C.cmarker(alpha),
        C.cexists(alpha),
        C.cexists(beta),
        C.cvar(x_, T.texists(alpha)),
      ]),
      E.subst(E.evar(x_), expr.arg, expr.body),
      T.texists(beta)
    );
    var broken = C.breakMarker(C.cmarker(alpha), r4.context);
    var delta = broken[0];
    var delta_ = broken[1];
    var tau = apply(delta_, T.tfun(T.texists(alpha), T.texists(beta)));
    var evars = C.unsolved(delta_);
    var r5 = freshTVars(r4.state, evars.length);
    var tvarssub =
      r5.tvars.map((x, i) => [T.tvar(x, evars[i].kind), evars[i].name]);
    var tvars = tvarssub.map(x => x[0]);
    return {
      state: r5.state,
      context: delta,
      type: T.tforalls(tvars, T.substs(tvarssub, tau)),
    };
  }
  if(expr.tag === E.EApp) {
    var r = typesynth(state, gamma, expr.left);
    return typeapplysynth(
      r.state,
      r.context,
      apply(r.context, r.type),
      expr.right
    );
  }
  if(expr.tag === E.EIf) {
    var r1 = typecheck(
      state,
      gamma,
      expr.cond,
      T.tbool
    );
    var r2 = freshTVar(r1.state);
    var tv = r2.tvar;
    var r3 = typecheck(
      r2.state,
      C.appendElems(r1.context, [
        C.cmarker(tv),
        C.cexists(tv),
      ]),
      expr.bodyTrue,
      T.texists(tv)
    );
    var r4 = typecheck(
      r3.state,
      r3.context,
      expr.bodyFalse,
      apply(r3.context, T.texists(tv))
    );
    return {
      state: r4.state,
      context: C.dropMarker(C.cmarker(tv), r4.context),
      type: apply(r4.context, T.texists(tv)),
    };
  }
  if(expr.tag === E.EFix) {
    var t = T.tvar('t');
    return {
      state,
      context: gamma,
      type: T.tforall(t, T.tfun(T.tfun(t, t), t)),
    };
  }
  throw new Error('typesynth failed on ' + expr);
};

var typeapplysynth = (state, gamma, type, e) => {
  // console.log('typeapplysynth', C.contextStr(gamma), T.str(type), E.str(e));
  checktypewf(gamma, type);
  if(type.tag === T.TForall) {
    var r = freshTVar(state);
    var alpha_ = r.tvar;
    var vkind = type.arg.kind;
    return typeapplysynth(
      r.state,
      C.snoc(gamma, C.cexists(alpha_, vkind)),
      T.subst(T.texists(alpha_, vkind), type.arg.name, type.type),
      e
    );
  }
  if(type.tag === T.TExists) {
    var r1 = freshTVar(state);
    var alpha1 = r1.tvar;
    var r2 = freshTVar(r1.state);
    var alpha2 = r2.tvar;
    var r3 = typecheck(
      r2.state,
      C.insertAt(gamma, C.cexists(type.name, type.kind), C.context([
        C.cexists(alpha2),
        C.cexists(alpha1),
        C.cexistssolved(type.name, T.tfun(T.texists(alpha1), T.texists(alpha2))),
      ])),
      e,
      T.texists(alpha1)
    );
    return {
      state: r3.state,
      context: r3.context,
      type: T.texists(alpha2),
    };
  }
  if(type.tag === T.TFun) {
    var r = typecheck(state, gamma, e, type.left);
    return {
      state: r.state,
      context: r.context,
      type: type.right,
    };
  }
  throw new Error('typeapplysynth failed on ' + type);
};

var infer = (expr, context, state) => {
  var r = typesynth(state || initialState, context || [], expr);
  return apply(r.context, r.type);
};

module.exports = {
  infer,
};
