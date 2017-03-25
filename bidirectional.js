// AST
var EVar = 'EVar';
var evar = name => ({
  tag: EVar,
  name,
});

var EUnit = 'EUnit';
var eunit = { tag: EUnit };

var EAbs = 'EAbs';
var eabs = (arg, body) => ({
  tag: EAbs,
  arg,
  body,
});

var EApp = 'EApp';
var eapp = (left, right) => ({
  tag: EApp,
  left,
  right,
});

var EAnno = 'EAnno';
var eanno = (expr, type) => ({
  tag: EAnno,
  expr,
  type,
});

var exprStr = e => {
  if(e.tag === EVar) return e.name;
  if(e.tag === EUnit) return '()';
  if(e.tag === EAbs) return '(\\' + e.arg + ' -> ' + exprStr(e.body) + ')';
  if(e.tag === EApp)
    return '(' + exprStr(e.left) + ' ' + exprStr(e.right) + ')';
  if(e.tag === EAnno)
    return '(' + exprStr(e.expr) + ' : ' + typeStr(e.type) + ')';
  throw new Error('Invalid expr in exprStr: ' + e);
};

var subst = (e1, x, e2) => {
  if(e2.tag === EVar) return e2.name === x? e1: e2;
  if(e2.tag === EUnit) return e2;
  if(e2.tag === EAbs)
    return e2.arg === x? e2: eabs(e2.arg, subst(e1, x, e2.body));
  if(e2.tag === EApp)
    return eapp(subst(e1, x, e2.left), subst(e1, x, e2.right));
  if(e2.tag === EAnno)
    return eanno(subst(e1, x, e2.expr), e2.type);
  throw new Error('Cannot subst over ' + e2);
};

var TUnit = 'TUnit';
var tunit = { tag: TUnit };

var TVar = 'TVar';
var tvar = name => ({
  tag: TVar,
  name,
});

var TExists = 'TExsts';
var texists = name => ({
  tag: TExists,
  name,
});

var TForall = 'TForall';
var tforall = (arg, type) => ({
  tag: TForall,
  arg,
  type,
});

var TFun = 'TFun';
var tfun = (left, right) => ({
  tag: TFun,
  left,
  right,
});

var tforalls = (args, type) =>
  args.reduceRight((t, arg) => tforall(arg, t), type);

var typeStr = t => {
  if(t.tag === TUnit) return '()';
  if(t.tag === TVar) return t.name;
  if(t.tag === TExists) return t.name + '^';
  if(t.tag === TForall) return '(forall ' + t.arg + ' . ' + typeStr(t.type) + ')';
  if(t.tag === TFun)
    return '(' + typeStr(t.left) + ' -> ' + typeStr(t.right) + ')';
  throw new Error('Invalid type in typeStr: ' + t);
};

var typeEq = (a, b) => {
  if(a.tag === TUnit) return b.tag === TUnit;
  if(a.tag === TVar) return b.tag === TVar && a.name === b.name;
  if(a.tag === TExists) return b.tag === TExists && a.name === b.name;
  if(a.tag === TForall)
    return b.tag === TForall && a.arg === b.arg && typeEq(a.type, b.type);
  if(a.tag === TFun)
    return b.tag === TFun && typeEq(a.left, b.left) && typeEq(a.right, b.right);
  throw new Error('Invalid type in typeEq: ' + a);
};

var isMonotype = t => {
  if(t.tag === TUnit) return true;
  if(t.tag === TVar) return true;
  if(t.tag === TForall) return false;
  if(t.tag === TExists) return true;
  if(t.tag === TFun) return isMonotype(t.left) && isMonotype(t.right);
  throw new Error('Cannot call isMonotype on ' + t);
};

var freeTVars = t => {
  if(t.tag === TUnit) return [];
  if(t.tag === TVar) return [t.name];
  if(t.tag === TForall) return freeTVars(t.type).filter(v => v !== t.arg);
  if(t.tag === TExists) return [t.name];
  if(t.tag === TFun) return freeTVars(t.left).concat(freeTVars(t.right));
  throw new Error('Cannot freeTVars on ' + t);
};

var typeSubst = (t1, v, t2) => {
  if(t2.tag === TUnit) return t2;
  if(t2.tag === TVar) return t2.name === v? t1: t2;
  if(t2.tag === TForall)
    return t2.arg === v? t2: tforall(t2.arg, typeSubst(t1, v, t2.type));
  if(t2.tag === TExists) return t2.name === v? t1: t2;
  if(t2.tag === TFun)
    return tfun(typeSubst(t1, v, t2.left), typeSubst(t1, v, t2.right));
  throw new Error('Cannot typeSubst over ' + t2);
};

var typeSubsts = (subs, type) =>
  subs.reduceRight((t, sub) => typeSubst(sub[0], sub[1], t), type);

var CForall = 'CForall';
var cforall = name => ({
  tag: CForall,
  name,
});

var CVar = 'CVar';
var cvar = (name, type) => ({
  tag: CVar,
  name,
  type,
});

var CExists = 'CExists';
var cexists = name => ({
  tag: CExists,
  name,
});

var CExistsSolved = 'CExistsSolved';
var cexistssolved = (name, type) => ({
  tag: CExistsSolved,
  name,
  type,
});

var CMarker = 'CMarker';
var cmarker = name => ({
  tag: CMarker,
  name,
});

var elemStr = e => {
  if(e.tag === CForall) return e.name;
  if(e.tag === CVar) return e.name + ' : ' + typeStr(e.type);
  if(e.tag === CExists) return e.name + '^';
  if(e.tag === CExistsSolved) return e.name + ' = ' + typeStr(e.type);
  if(e.tag === CMarker) return '|>' + e.name + '^';
  throw new Error('Invalid elem in elemStr: ' + e);
};

var contextStr = c => '[' + c.map(elemStr).join(', ') + ']';

var elemEq = (a, b) => {
  if(a.tag === CForall) return b.tag === CForall && a.name === b.name;
  if(a.tag === CVar)
    return b.tag === CVar && a.name === b.name && typeEq(a.type, b.type);
  if(a.tag === CExists) return b.tag === CExists && a.name === b.name;
  if(a.tag === CExistsSolved)
    return b.tag === CExistsSolved &&
      a.name === b.name && typeEq(a.type, b.type);
  if(a.tag === CMarker) return b.tag === CMarker && a.name === b.name;
  throw new Error('Invalid elem in elemEq: ' + a);
};

var isComplete = c => {
  for(var i = 0, l = c.length; i < l; i++)
    if(c[i].tag === CExists) return false;
  return true;
};

var snoc = (c, e) => [e].concat(c);
var empty = [];
var append = (a, b) => b.concat(a);
var appendElems = (c, es) => append(c, es);
var context = c => c.slice(0).reverse();
var dropMarker = (m, g) => {
  for(var i = 0, l = g.length; i < l; i++)
    if(elemEq(g[i], m)) return g.slice(i + 1);
  return [];
};
var breakMarker = (m, g) => {
  for(var i = 0, l = g.length; i < l; i++)
    if(elemEq(g[i], m)) return [g.slice(0, i), g.slice(i + 1)];
  return [g, []];
};

// Context
var contains = (v, a) => a.indexOf(v) >= 0;

var existentials = c =>
  c.filter(e => e.tag === CExists || e.tag === CExistsSolved).map(x => x.name);

var unsolved = c =>
  c.filter(e => e.tag === CExists).map(x => x.name);

var vars = c =>
  c.filter(e => e.tag === CVar).map(x => x.name);

var foralls = c =>
  c.filter(e => e.tag === CForall).map(x => x.name);

var markers = c =>
  c.filter(e => e.tag === CMarker).map(x => x.name);

var wf = c => {
  if(c.length === 0) return true;
  var rest = c.slice(1);
  if(!wf(rest)) return false;
  var e = c[0];
  if(e.tag === CForall) return !contains(e.name, foralls(rest));
  if(e.tag === CVar)
    return !contains(e.name, vars(rest)) && typewf(rest, e.type);
  if(e.tag === CExists)
    return !contains(e.name, existentials(rest));
  if(e.tag === CExistsSolved)
    return !contains(e.name, existentials(rest)) && typewf(rest, e.type);
  if(e.tag === CMarker)
    return !contains(e.name, markers(rest)) &&
      !contains(e.name, existentials(rest));
  throw new Error('Invalid element in Context: ' + e);
};

var typewf = (c, t) => {
  if(t.tag === TVar) return contains(t.name, foralls(c));
  if(t.tag === TUnit) return true;
  if(t.tag === TFun) return typewf(c, t.left) && typewf(c, t.right);
  if(t.tag === TForall) return typewf(snoc(c, cforall(t.arg)), t.type);
  if(t.tag === TExists) return contains(t.name, existentials(c));
  throw new Error('Invalid type in typwf: ' + t);
};

var checkwf = c => {
  if(!wf(c)) throw new Error('Malformed context ' + contextStr(c));
};

var checktypewf = (c, t) => {
  if(!typewf(c, t)) throw new Error('Malformed type ' + typeStr(t));
  checkwf(c);
};

var findSolved = (c, v) => {
  var x = c.find(x => x.tag === CExistsSolved && x.name === v);
  return x? x.type: null;
};

var findVarType = (c, v) => {
  var x = c.find(x => x.tag === CVar && x.name === v);
  return x? x.type: null;
};

var solve = (c, v, t) => {
  var broken = breakMarker(cexists(v), c);
  var gammaL = broken[0];
  var gammaR = broken[1];
  if(typewf(gammaL, t))
    return append(appendElems(gammaL, [cexistssolved(v, t)]), gammaR);
  return null;
};

var insertAt = (gamma, c, theta) => {
  var broken = breakMarker(c, gamma);
  return append(broken[0], append(theta, broken[1]));
};

var apply = (gamma, t) => {
  if(t.tag === TUnit) return t;
  if(t.tag === TVar) return t;
  if(t.tag === TForall) return tforall(t.arg, apply(gamma, t.type));
  if(t.tag === TExists) {
    var solved = findSolved(gamma, t.name);
    if(!solved) return t;
    return apply(gamma, solved);
  }
  if(t.tag === TFun) return tfun(apply(gamma, t.left), apply(gamma, t.right));
  throw new Error('Invalid type in apply: ' + t);
};

var ordered = (gamma, alpha, beta) =>
  contains(alpha, existentials(dropMarker(cexists(beta), gamma)));

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
  var: "'" + state.tvar,
  state: clone(state, 'tvar', state.tvar + 1),
});
var freshTVars = (state, n) => {
  var r = [];
  for(var i = 0; i < n; i++) r.push("'" + state.tvar + i);
  return {
    tvars: r,
    state: clone(state, 'tvar', state.tvar + n),
  }
};

// Type
var subtype = (state, gamma, t1, t2) => {
  checktypewf(gamma, t1);
  checktypewf(gamma, t2);
  if(t1.tag === TVar && t2.tag === TVar && t1.name === t2.name)
    return { state, context: gamma };
  if(t1.tag === TUnit && t2.tag === TUnit)
    return { state, context: gamma };
  if(t1.tag === TExists && t2.tag === TExists
    && t1.name === t2.name
    && contains(t1.name, existentials(gamma)))
    return { state, context: gamma };
  if(t1.tag === TFun && t2.tag === TFun) {
    var r = subtype(state, gamma, t2.left, t1.left);
    return subtype(r.state, r.context, t1.right, t2.right);
  }
  if(t2.tag === TForall) {
    var r1 = freshTVar(state);
    var v = r1.tvar;
    var r2 = subtype(
      r1.state,
      snoc(gamma, cforall(v)),
      t1,
      typeSubst(tvar(v), t2.arg, t2.type)
    );
    return {
      state: r2.state,
      context: dropMarker(cforall(v), r2.context),
    };
  }
  if(t1.tag === TForall) {
    var r1 = freshTVar(state);
    var v = r1.tvar;
    var r2 = subtype(
      r1.state,
      appendElems(gamma, [cmarker(v), cexists(v)]),
      typeSubst(texists(v), t1.arg, t1.type),
      t2
    );
    return {
      state: r2.state,
      context: dropMarker(cmarker(v), r2.context),
    }
  }
  if(t1.tag === TExists
    && contains(t1.name, existentials(gamma))
    && !contains(t1.name, freeTVars(t2))) {
    return instantiateL(state, gamma, t1.name, t2);
  }
  if(t2.tag === TExists
    && contains(t2.name, existentials(gamma))
    && !contains(t2.name, freeTVars(t1))) {
    return instantiateR(state, gamma, t1, t2.name);
  }
  throw new Error('subtype failed');
};

var instantiateL = (state, gamma, alpha, a) => {
  checktypewf(gamma, a);
  checktypewf(gamma, texists(alpha));
  var gamma_ = isMonotype(a)? solve(gamma, alpha, a): null;
  if(gamma_) return { state, context: gamma_ };
  if(a.tag === TExists) {
    if(ordered(gamma, alpha, a.name)) {
      var solved = solve(gamma, a.name, texists(alpha));
      if(!solved) throw new Error('instantiateL failed');
      return { state, context: solved };
    } else {
      var solved = solve(gamma, alpha, texists(a.name));
      if(!solved) throw new Error('instantiateL failed');
      return { state, context: solved };
    }
  }
  if(a.tag === TFun) {
    var r1 = freshTVar(state);
    var alpha1 = r1.tvar;
    var r2 = freshTVar(r1.state);
    var alpha2 = r2.tvar;
    var r3 = instantiateR(
      r2.state,
      insertAt(gamma, cexists(alpha), [
        cexists(alpha2),
        cexists(alpha1),
        cexistssolved(alpha, tfun(texists(alpha1), texists(alpha2))),
      ]),
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
  if(a.tag === TForall) {
    var r1 = freshTVar(state);
    var beta_ = r1.tvar;
    var r2 = instantiateL(
      r1.state,
      appendElems(gamma, [cforall(beta_)]),
      alpha,
      typeSubst(tvar(beta_), a.arg, a.type)
    );
    return {
      state: r2.state,
      context: dropMarker(cforall(beta_), r2.context),
    };
  }
  throw new Error('instantiateL failed');
};

var instantiateR = (state, gamma, a, alpha) => {
  checktypewf(gamma, a);
  checktypewf(gamma, texists(alpha));
  var gamma_ = isMonotype(a)? solve(gamma, alpha, a): null;
  if(gamma_) return { state, context: gamma_ };
  if(a.tag === TExists) {
    if(ordered(gamma, alpha, a.name)) {
      var solved = solve(gamma, a.name, texists(alpha));
      if(!solved) throw new Error('instantiateR failed');
      return { state, context: solved };
    } else {
      var solved = solve(gamma, alpha, texists(a.name));
      if(!solved) throw new Error('instantiateR failed');
      return { state, context: solved };
    }
  }
  if(a.tag === TFun) {
    var r1 = freshTVar(state);
    var alpha1 = r1.tvar;
    var r2 = freshTVar(r1.state);
    var alpha2 = r2.tvar;
    var r3 = instantiateL(
      r2.state,
      insertAt(gamma, cexists(alpha), [
        cexists(alpha2),
        cexists(alpha1),
        cexistssolved(alpha, tfun(texists(alpha1), texists(alpha2))),
      ]),
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
  if(a.tag === TForall) {
    var r1 = freshTVar(state);
    var beta_ = r1.tvar;
    var r2 = instantiateR(
      r1.state,
      appendElems(gamma, [cmarker(beta_), cexists(beta_)]),
      typeSubst(texists(beta_), a.arg, a.type),
      alpha
    );
    return {
      state: r2.state,
      context: dropMarker(cmarker(beta_), r2.context),
    };
  }
  throw new Error('instantiateR failed');
};

var typecheck = (state, gamma, expr, type) => {
  checktypewf(gamma, type);
  if(expr.tag === EUnit && type.tag === TUnit)
    return { state, context: gamma };
  if(type.tag === TForall) {
    var r1 = freshTVar(state);
    var alpha_ = r1.tvar;
    var r2 = typecheck(
      r1.state,
      snoc(gamma, cforall(alpha_)),
      expr,
      typeSubst(tvar(alpha_), type.arg, type.type)
    );
    return {
      state: r2.state,
      context: dropMarker(cforall(alpha_), r2.context),
    };
  }
  if(expr.tag === EAbs && type.tag === TFun) {
    var r1 = freshVar(state);
    var x_ = r1.var;
    var r2 = typecheck(
      r1.state,
      snoc(gamma, cvar(x_, type.left)),
      subst(evar(x_), expr.arg, expr.body),
      type.right
    );
    return {
      state: r2.state,
      context: dropMarker(cvar(x_, type.left), r2.context),
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
  checkwf(gamma);
  if(expr.tag === EVar) {
    var type = findVarType(gamma, expr.name);
    if(!type) throw new Error('Not in scope ' + expr.name);
    return {
      state,
      context: gamma,
      type,
    };
  }
  if(expr.tag === EAnno) {
    var r = typecheck(state, gamma, expr.expr, expr.type);
    return {
      state: r.state,
      context: r.context,
      type: expr.type,
    };
  }
  if(expr.tag === EUnit)
    return { state, context: gamma, type: TUnit };
  if(expr.tag === EAbs) {
    var r1 = freshVar(state);
    var x_ = r1.var;
    var r2 = freshTVar(r1.state);
    var alpha = r2.tvar;
    var r3 = freshTVar(r2.state);
    var beta = r3.tvar;
    var r4 = typecheck(
      r3.state,
      appendElems(gamma, [
        cmarker(alpha),
        cexists(alpha),
        cexists(beta),
        cvar(x_, texists(alpha)),
      ]),
      subst(evar(x_), expr.arg, expr.body),
      texists(beta)
    );
    var broken = breakMarker(cmarker(alpha), r4.context);
    var delta = broken[0];
    var delta_ = broken[1];
    var tau = apply(delta_, tfun(texists(alpha), texists(beta)));
    var evars = unsolved(delta_);
    var r5 = freshTVars(r4.state, evars.length);
    return {
      state: r5.state,
      context: delta,
      type: tforalls(
        r5.tvars,
        typeSubsts(r5.tvars.map((x, i) => [tvar(x), evars[i]]), tau)
      ),
    };
  }
  if(expr.tag === EApp) {
    var r = typesynth(state, gamma, expr.left);
    return typeapplysynth(
      r.state,
      r.context,
      apply(r.context, r.type),
      expr.right
    );
  }
  throw new Error('typesynth failed on ' + expr);
};

var typeapplysynth = (state, gamma, type, e) => {
  checktypewf(gamma, type);
  if(type.tag === TForall) {
    var r = freshTVar(state);
    var alpha_ = r.tvar;
    return typeapplysynth(
      r.state,
      snoc(gamma, cexists(alpha_)),
      typeSubst(texists(alpha_), type.arg, type.type),
      e
    );
  }
  if(type.tag === TExists) {
    var r1 = freshTVar(state);
    var alpha1 = r1.tvar;
    var r2 = freshTVar(r1.state);
    var alpha2 = r2.tvar;
    var r3 = typecheck(
      r2.state,
      insertAt(gamma, [
        cexists(alpha2),
        cexists(alpha1),
        cexistssolved(alpha, tfun(texists(alpha1), texists(alpha2))),
      ]),
      e,
      texists(alpha1)
    );
    return {
      state: r3.state,
      context: r3.context,
      type: texists(alpha2),
    };
  }
  if(type.tag === TFun) {
    var r = typecheck(state, gamma, e, type.left);
    return {
      state: r.state,
      context: r.context,
      type: type.right,
    };
  }
  throw new Error('typeapplysynth failed on ' + type);
};

var infer = expr => {
  var r = typesynth(initialState, [], expr);
  return apply(r.context, r.type);
};

var eid = eanno(eabs('x', evar('x')), tforall('t', tfun(tvar('t'), tvar('t'))));
console.log(exprStr(eid));
var t = infer(eid);
console.log(typeStr(t));
