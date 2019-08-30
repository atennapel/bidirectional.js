/**
 * Minimal implementation of type inference for predicative System F
 * This algorithm should function the same as the algorithm from
 * "Complete and easy bidirectional typechecking for higher-rank polymorphism"
 */
// util
const terr = msg => { throw new TypeError(msg) };

// list
const Nil = { tag: 'Nil' };
const Cons = (head, tail) => ({ tag: 'Cons', head, tail });

const showList = (l, str = x => `${x}`) => {
  const r = [];
  while (l.tag === 'Cons') {
    r.push(str(l.head));
    l = l.tail;
  }
  return `[${r.join(', ')}]`;
};

const contains = (l, x) =>
  l.tag === 'Cons' ? l.head === x || contains(l.tail, x) : false;

const subset = (a, b) =>
  a.tag === 'Cons' ? (contains(b, a.head) ? subset(a.tail, b) : false) : true;

const lookup = (l, x) =>
  l.tag === 'Cons' ? (l.head[0] === x ? l.head[1] : lookup(l.tail, x)) : null;

const fromArray = a => {
  let l = Nil;
  for (let i = a.length - 1; i >= 0; i--) l = Cons(a[i], l);
  return l;
};

// terms
const Var = name => ({ tag: 'Var', name });
const Abs = (name, body) => ({ tag: 'Abs', name, body });
const AbsAnn = (name, type, body) =>
  ({ tag: 'AbsAnn', name, type, body });
const App = (left, right) => ({ tag: 'App', left, right });
const Ann = (term, type) => ({ tag: 'Ann', term, type });
const AbsT = (name, body) => ({ tag: 'AbsT', name, body });
const AppT = (left, right) => ({ tag: 'AppT', left, right });

const showTerm = t => {
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Abs') return `(\\${t.name}. ${showTerm(t.body)})`;
  if (t.tag === 'AbsAnn')
    return `(\\(${t.name} : ${showType(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'App')
    return `(${showTerm(t.left)} ${showTerm(t.right)})`;
  if (t.tag === 'Ann')
    return `(${showTerm(t.term)} : ${showType(t.type)})`;
  if (t.tag === 'AbsT') return `(/\\${t.name}. ${showTerm(t.body)})`;
  if (t.tag === 'AppT')
    return `(${showTerm(t.left)} @(${showType(t.right)}))`;
};

const pruneInTerm = (t, map = {}) => {
  if (t.tag === 'Abs') return Abs(t.name, pruneInTerm(t.body, map));
  if (t.tag === 'AbsAnn')
    return AbsAnn(t.name, prune(t.type, map), pruneInTerm(t.body, map));
  if (t.tag === 'App')
    return App(pruneInTerm(t.left, map), pruneInTerm(t.right, map));
  if (t.tag === 'Ann')
    return Ann(pruneInTerm(t.term, map), prune(t.type, map));
  if (t.tag === 'AbsT') return AbsT(t.name, pruneInTerm(t.body, map));
  if (t.tag === 'AppT')
    return AppT(pruneInTerm(t.left, map), prune(t.right, map));
  return t;
};

// types
const TVar = name => ({ tag: 'TVar', name });
const TForall = (name, body) => ({ tag: 'TForall', name, body });
const TFun = (left, right) => ({ tag: 'TFun', left, right });
const TMeta = (id, tvs) => ({ tag: 'TMeta', id, tvs, type: null });
const TSkol = id => ({ tag: 'TSkol', id });

let _tmetaid = 0;
const resetTMetaId = () => { _tmetaid = 0 };
const freshTMeta = tvs => TMeta(_tmetaid++, tvs);

let _tskolid = 0;
const resetTSkolId = () => { _tskolid = 0 };
const freshTSkol = () => TSkol(_tskolid++);

const showType = t => {
  if (t.tag === 'TVar') return t.name;
  if (t.tag === 'TMeta')
    return `?${t.id}${showList(t.tvs)}${t.type ? `{${showType(t.type)}}` : ''}`;
  if (t.tag === 'TSkol') return `'${t.id}`;
  if (t.tag === 'TForall')
    return `(forall ${t.name}. ${showType(t.body)})`;
  if (t.tag === 'TFun')
    return `(${showType(t.left)} -> ${showType(t.right)})`;
};

const prune = (t, map = {}) => {
  if (t.tag === 'TMeta') return t.type ? t.type = prune(t.type, map) : t;
  if (t.tag === 'TFun')
    return TFun(prune(t.left, map), prune(t.right, map));
  if (t.tag === 'TForall') return TForall(t.name, prune(t.body, map));
  if (t.tag === 'TSkol') return map[t.id] ? TVar(map[t.id]) : t;
  return t;
};

const substTVar = (x, s, t) => {
  if (t.tag === 'TVar') return t.name === x ? s : t;
  if (t.tag === 'TMeta' && t.type) return substTVar(x, s, t.type);
  if (t.tag === 'TFun')
    return TFun(substTVar(x, s, t.left), substTVar(x, s, t.right));
  if (t.tag === 'TForall')
    return t.name === x ? t : TForall(t.name, substTVar(x, s, t.body));
  return t;
};
const openTForall = (f, t) => substTVar(f.name, t, f.body);

const containsTMeta = (t, m) => {
  if (t === m) return true;
  if (t.tag === 'TMeta' && t.type) return containsTMeta(t.type, m);
  if (t.tag === 'TFun')
    return containsTMeta(t.left, m) || containsTMeta(t.right, m);
  if (t.tag === 'TForall') return containsTMeta(t.body, m);
  return false;
};

// subtyping
const subtypeTMeta = (tvs, m, t, left, term) => {
  console.log(`subtypeTMeta ${showType(m)} := ${showType(t)}`);
  if (t.tag === 'TFun') {
    if (containsTMeta(t, m))
      return terr(`occurs failed: ${showType(m)} := ${showType(t)}`);
    const a = freshTMeta(m.tvs);
    const b = freshTMeta(m.tvs);
    const ty = TFun(a, b);
    m.type = ty;
    return left ? subtype(tvs, ty, t, term) : subtype(tvs, t, ty, term);
  }
  if (t.tag === 'TMeta') {
    if (m === t) return;
    if (t.type) return subtypeTMeta(tvs, m, t.type, left, term);
    if (!subset(m.tvs, t.tvs))
      return terr(`subset failed: ${showType(m)} := ${showType(t)}`);
    m.type = t;
    return term;
  }
  if (t.tag === 'TSkol') {
    if (!contains(m.tvs, t.id))
      return terr(`tvar out of scope: ${showType(m)} := ${showType(t)}`);
    m.type = t;
    return term;
  }
  if (t.tag === 'TVar') {
    m.type = t;
    return term;
  }
  return terr(`subtype unexpected type: ${showType(m)} := ${showType(t)}`);
};

const subtype = (tvs, a, b, term) => {
  console.log(`subtype ${showType(a)} <: ${showType(b)}`);
  if (a === b) return term;
  if (a.tag === 'TVar' && b.tag === 'TVar' && a.name === b.name)
    return term;
  if (a.tag === 'TFun' && b.tag === 'TFun') {
    const term1 = subtype(tvs, b.left, a.left, term);
    const term2 = subtype(tvs, a.right, b.right, term1);
    return term2;
  }
  if (b.tag === 'TForall') {
    const sk = freshTSkol();
    skolmap[sk.id] = b.name;
    const body = subtype(Cons(sk.id, tvs), a, openTForall(b, sk), term);
    return AbsT(b.name, body);
  }
  if (a.tag === 'TForall') {
    const m = freshTMeta(tvs);
    const body = subtype(tvs, openTForall(a, m), b, term);
    return AppT(body, m);
  }
  if (a.tag === 'TMeta') {
    if (a.type) return subtype(tvs, a.type, b, term);
    return subtypeTMeta(tvs, a, b, true, term);
  }
  if (b.tag === 'TMeta') {
    if (b.type) return subtype(tvs, a, b.type, term);
    return subtypeTMeta(tvs, b, a, false, term);
  }
  return terr(`failed ${showType(a)} <: ${showType(b)}`);
};

// inference
let _varid = 0;
const resetVarId = () => { _varid = 0 };
const freshVar = () => Var(_varid++);

let skolmap = {};

const synth = (env, tvs, t) => {
  console.log(`synth ${showTerm(t)}`);
  if (t.tag === 'Var') {
    const ty = lookup(env, t.name);
    if (!t) return terr(`undefined var ${t.name}`);
    return [ty, t];
  }
  if (t.tag === 'Ann') {
    const term = check(env, tvs, t.term, t.type);
    return [t.type, term];
  }
  if (t.tag === 'App') {
    const [ty, left] = synth(env, tvs, t.left);
    return synthapp(env, tvs, ty, t.right, left);
  }
  if (t.tag === 'Abs') {
    const a = freshTMeta(tvs);
    const b = freshTMeta(tvs);
    const body = check(Cons([t.name, a], env), tvs, t.body, b);
    return [TFun(a, b), AbsAnn(t.name, a, body)];
  }
  if (t.tag === 'AbsAnn') {
    const b = freshTMeta(tvs);
    const body = check(Cons([t.name, t.type], env), tvs, t.body, b);
    return [TFun(t.type, b), AbsAnn(t.name, t.type, body)];
  }
  if (t.tag === 'AbsT') {
    const ntvs = Cons(t.name, tvs);
    const b = freshTMeta(ntvs);
    const body = check(env, ntvs, t.body, b);
    return [TForall(t.name, b), AbsT(t.name, body)];
  }
  if (t.tag === 'AppT') {
    const [ty, left] = synth(env, tvs, t.left);
    const f = prune(ty);
    if (f.tag !== 'TForall')
      return terr(`not a forall in ${showTerm(t)} but ${showType(f)}`);
    return [openTForall(f, t.right), AppT(left, t.right)];
  }
  return terr(`cannot synth ${showTerm(t)}`);
};

const check = (env, tvs, t, ty) => {
  console.log(`check ${showTerm(t)} : ${showType(ty)}`);
  if (ty.tag === 'TMeta' && ty.type) return check(env, tvs, t, ty.type);
  if (ty.tag === 'TForall') {
    const sk = freshTSkol();
    skolmap[sk.id] = ty.name;
    const rest = check(env, Cons(sk.id, tvs), t, openTForall(ty, sk));
    return AbsT(ty.name, rest);
  }
  if (t.tag === 'Abs' && ty.tag === 'TFun') {
    const body = check(Cons([t.name, ty.left], env), tvs, t.body, ty.right);
    return AbsAnn(t.name, ty.left, body);
  }
  const [inf, elab] = synth(env, tvs, t);
  const elab1 = subtype(tvs, inf, ty, elab);
  return elab1;
};

const synthapp = (env, tvs, ty, t, app) => {
  console.log(`synthapp ${showType(ty)} @ ${showTerm(t)}`);
  if (ty.tag === 'TForall') {
    const m = freshTMeta(tvs);
    return synthapp(env, tvs, openTForall(ty, m), t, AppT(app, m));
  }
  if (ty.tag === 'TFun') {
    const arg = check(env, tvs, t, ty.left);
    return [ty.right, App(app, arg)];
  }
  if (ty.tag === 'TMeta') {
    if (ty.type) return synthapp(env, tvs, ty.type, t, app);
    const a = freshTMeta(ty.tvs);
    const b = freshTMeta(ty.tvs);
    ty.type = TFun(a, b);
    const arg = check(env, tvs, t, a);
    return [b, App(app, arg)];
  }
  return terr(`cannot synthapp ${showType(ty)} @ ${showTerm(t)}`);
};

const infer = (env, t) => {
  resetTMetaId();
  resetTSkolId();
  resetVarId();
  skolmap = {};
  const [ty, term] = synth(env, Nil, t);
  return [prune(ty), pruneInTerm(term, skolmap)];
};

// testing
const v = Var;
const tv = TVar;
const tid = TForall('t', TFun(tv('t'), tv('t')));

const env = fromArray([
  ['id', tid],
  ['Z', tv('Int')],
  ['add', TFun(tv('Int'), TFun(tv('Int'), tv('Int')))],
]);

const term = Ann(Abs('x', Abs('y', v('x'))), TForall('t', TFun(tv('t'), TForall('r', TFun(tv('r'), tv('t'))))));
console.log(showTerm(term));
const [ty, term1] = infer(env, term);
console.log(showType(ty));
console.log(showTerm(term1));
