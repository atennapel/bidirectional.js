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
const AbsAnn = (name, type, body) => ({ tag: 'Abs', name, type, body });
const App = (left, right) => ({ tag: 'App', left, right });
const Ann = (term, type) => ({ tag: 'Ann', term, type });
const AbsT = (name, body) => ({ tag: 'AbsT', name, body });
const AppT = (left, right) => ({ tag: 'AppT', left, right });

const showTerm = t => {
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Abs') return `(\\${t.name}. ${showTerm(t.body)})`;
  if (t.tag === 'AbsAnn') return `(\\(${t.name} : ${showType(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'App') return `(${showTerm(t.left)} ${showTerm(t.right)})`;
  if (t.tag === 'Ann') return `(${showTerm(t.term)} : ${showType(t.type)})`;
  if (t.tag === 'AbsT') return `(/\\${t.name}. ${showTerm(t.body)})`;
  if (t.tag === 'AppT') return `(${showTerm(t.left)} @(${showType(t.right)}))`;
};

// types
const TVar = name => ({ tag: 'TVar', name });
const TForall = (name, body) => ({ tag: 'TForall', name, body });
const TFun = (left, right) => ({ tag: 'TFun', left, right });
const TApp = (left, right) => ({ tag: 'TApp', left, right });
const TMeta = (id, tvs) => ({ tag: 'TMeta', id, tvs, type: null });

let _tmetaid = 0;
const resetTMetaId = () => { _tmetaid = 0 };
const freshTMeta = tvs => TMeta(_tmetaid++, tvs);

const showType = t => {
  if (t.tag === 'TVar') return t.name;
  if (t.tag === 'TMeta') return `?${t.id}${showList(t.tvs)}${t.type ? `{${showType(t.type)}}` : ''}`;
  if (t.tag === 'TForall') return `(forall ${t.name}. ${showType(t.body)})`;
  if (t.tag === 'TFun') return `(${showType(t.left)} -> ${showType(t.right)})`;
  if (t.tag === 'TApp') return `(${showType(t.left)} ${showType(t.right)})`;
};

const prune = t => {
  if (t.tag === 'TMeta') return t.type ? t.type = prune(t.type) : t;
  if (t.tag === 'TFun') return TFun(prune(t.left), prune(t.right));
  if (t.tag === 'TApp') return TApp(prune(t.left), prune(t.right));
  if (t.tag === 'TForall') return TForall(t.name, prune(t.body));
  return t;
};

const substTVar = (x, s, t) => {
  if (t.tag === 'TVar') return t.name === x ? s : t;
  if (t.tag === 'TMeta' && t.type) return substTVar(x, s, t.type);
  if (t.tag === 'TFun')
    return TFun(substTVar(x, s, t.left), substTVar(x, s, t.right));
  if (t.tag === 'TApp')
    return TApp(substTVar(x, s, t.left), substTVar(x, s, t.right));
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
  if (t.tag === 'TApp')
    return containsTMeta(t.left, m) || containsTMeta(t.right, m);
  if (t.tag === 'TForall') return containsTMeta(t.body, m);
  return false;
};

const freetvsR = (t, m) => {
  if (t.tag === 'TVar') return m[t.name] = true;
  if (t.tag === 'TFun') {
    freetvsR(t.left, m);
    freetvsR(t.right, m);
    return;
  }
  if (t.tag === 'TApp') {
    freetvsR(t.left, m);
    freetvsR(t.right, m);
    return;
  }
  if (t.tag === 'TForall') {
    freetvsR(t.body, m);
    m[t.name] = false;
    return;
  }
};
const freetvs = t => {
  const m = {};
  freetvsR(t, m);
  let l = Nil;
  for (let k in m) if (m[k]) l = Cons(k, l);
  return l;
};

// subtyping
const subtypeTMeta = (tvs, m, t, left) => {
  console.log(`subtypeTMeta ${showType(m)} := ${showType(t)}`);
  if (t.tag === 'TFun') {
    const a = freshTMeta(m.tvs);
    const b = freshTMeta(m.tvs);
    const ty = TFun(a, b);
    m.type = ty;
    left ? subtype(tvs, ty, t) : subtype(tvs, t, ty);
    return;
  }
  if (t.tag === 'TApp') {
    const a = freshTMeta(m.tvs);
    const b = freshTMeta(m.tvs);
    const ty = TApp(a, b);
    m.type = ty;
    left ? subtype(tvs, ty, t) : subtype(tvs, t, ty);
    return;
  }
  if (t.tag === 'TMeta') {
    if (m === t) return;
    if (t.type) return subtypeTMeta(tvs, m, t.type, left);
    if (!subset(m.tvs, t.tvs))
      return terr(`subset failed: ${showType(m)} := ${showType(t)}`);
  }
  if (containsTMeta(t, m))
    return terr(`occurs failed: ${showType(m)} := ${showType(t)}`);
  if (!subset(freetvs(t), m.tvs))
    return terr(`out of scope tvar: ${showType(m)} := ${showType(t)}`);
  m.type = t;
};

const subtype = (tvs, a, b) => {
  console.log(`subtype ${showType(a)} <: ${showType(b)}`);
  if (a.tag === 'TVar' && b.tag === 'TVar' && a.name === b.name) return;
  if (a.tag === 'TFun' && b.tag === 'TFun') {
    subtype(tvs, b.left, a.left);
    subtype(tvs, a.right, b.right);
    return;
  }
  if (a.tag === 'TApp' && b.tag === 'TApp') {
    subtype(tvs, a.left, b.left);
    subtype(tvs, b.left, a.left);
    subtype(tvs, a.right, b.right);
    subtype(tvs, b.right, a.right);
    return;
  }
  if (b.tag === 'TForall') {
    subtype(Cons(b.name, tvs), a, b.body);
    return;
  }
  if (a.tag === 'TForall') {
    const m = freshTMeta(tvs);
    subtype(tvs, openTForall(a, m), b);
    return;
  }
  if (a.tag === 'TMeta') {
    if (a.type) return subtype(tvs, a.type, b);
    return subtypeTMeta(tvs, a, b, true);
  }
  if (b.tag === 'TMeta') {
    if (b.type) return subtype(tvs, a, b.type);
    return subtypeTMeta(tvs, b, a, false);
  }
  return terr(`failed ${showType(a)} <: ${showType(b)}`);
};

// inference
const synth = (env, tvs, t) => {
  console.log(`synth ${showTerm(t)}`);
  if (t.tag === 'Var') {
    const ty = lookup(env, t.name);
    if (!t) return terr(`undefined var ${t.name}`);
    return ty;
  }
  if (t.tag === 'Ann') {
    check(env, tvs, t.term, t.type);
    return t.type;
  }
  if (t.tag === 'App') {
    const ty = synth(env, tvs, t.left);
    return synthapp(env, tvs, ty, t.right);
  }
  if (t.tag === 'Abs') {
    const a = freshTMeta(tvs);
    const b = freshTMeta(tvs);
    check(Cons([t.name, a], env), tvs, t.body, b);
    return TFun(a, b);
  }
  if (t.tag === 'AbsAnn') {
    const b = freshTMeta(tvs);
    check(Cons([t.name, t.type], env), tvs, t.body, b);
    return TFun(t.type, b);
  }
  if (t.tag === 'AbsT') {
    const ntvs = Cons(t.name, tvs);
    const b = freshTMeta(ntvs);
    check(env, ntvs, t.body, b);
    return TForall(t.name, b);
  }
  if (t.tag === 'AppT') {
    const f = prune(synth(env, tvs, t.left));
    if (f.tag !== 'TForall')
      return terr(`not a forall in ${showTerm(t)} but ${showType(f)}`);
    return openTForall(f, t.right);
  }
  return terr(`cannot synth ${showTerm(t)}`);
};

const check = (env, tvs, t, ty) => {
  console.log(`check ${showTerm(t)} : ${showType(ty)}`);
  if (ty.tag === 'TForall') {
    check(env, Cons(ty.name, tvs), t, ty.body);
    return;
  }
  if (t.tag === 'Abs' && ty.tag === 'TFun') {
    check(Cons([t.name, ty.left], env), tvs, t.body, ty.right);
    return;
  }
  const inf = synth(env, tvs, t);
  subtype(tvs, inf, ty);
};

const synthapp = (env, tvs, ty, t) => {
  console.log(`synthapp ${showType(ty)} @ ${showTerm(t)}`);
  if (ty.tag === 'TForall') {
    const m = freshTMeta(tvs);
    return synthapp(env, tvs, openTForall(ty, m), t);
  }
  if (ty.tag === 'TFun') {
    check(env, tvs, t, ty.left);
    return ty.right;
  }
  if (ty.tag === 'TMeta') {
    if (ty.type) return synthapp(env, tvs, ty.type, t);
    const a = freshTMeta(ty.tvs);
    const b = freshTMeta(ty.tvs);
    ty.type = TFun(a, b);
    check(env, tvs, t, a);
    return b;
  }
  return terr(`cannot synthapp ${showType(ty)} @ ${showTerm(t)}`);
};

const infer = (env, tvs, t) => {
  resetTMetaId();
  const ty = synth(env, tvs, t);
  return prune(ty);
};

// testing
const v = Var;
const tv = TVar;
const tid = TForall('t', TFun(tv('t'), tv('t')));

const env = fromArray([
  ['id', tid],
  ['single', TForall('t', TFun(tv('t'), TApp(tv('List'), tv('t'))))],
  ['ids', TApp(tv('List'), tid)],
  ['rcons', TForall('t', TFun(TApp(tv('List'), tv('t')), TFun(tv('t'), TApp(tv('List'), tv('t')))))],
  ['cons', TForall('t', TFun(tv('t'), TFun(TApp(tv('List'), tv('t')), TApp(tv('List'), tv('t')))))],
]);
const tvs = fromArray(['List']);

const term = Abs('x', Abs('y', v('x')));
console.log(showTerm(term));
const ty = infer(env, tvs, term);
console.log(showType(ty));
