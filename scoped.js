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
const App = (left, right) => ({ tag: 'App', left, right });
const Ann = (term, type) => ({ tag: 'Ann', term, type });

const showTerm = t => {
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Abs') return `(\\${t.name}. ${showTerm(t.body)})`;
  if (t.tag === 'App')
    return `(${showTerm(t.left)} ${showTerm(t.right)})`;
  if (t.tag === 'Ann')
    return `(${showTerm(t.term)} : ${showType(t.type)})`;
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

const prune = t => {
  if (t.tag === 'TMeta') return t.type ? t.type = prune(t.type) : t;
  if (t.tag === 'TFun') return TFun(prune(t.left), prune(t.right));
  if (t.tag === 'TForall') return TForall(t.name, prune(t.body));
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
const subtypeTMeta = (tvs, m, t, left) => {
  console.log(`subtypeTMeta ${showType(m)} := ${showType(t)}`);
  if (t.tag === 'TFun') {
    if (containsTMeta(t, m))
      return terr(`occurs failed: ${showType(m)} := ${showType(t)}`);
    const a = freshTMeta(m.tvs);
    const b = freshTMeta(m.tvs);
    const ty = TFun(a, b);
    m.type = ty;
    left ? subtype(tvs, ty, t) : subtype(tvs, t, ty);
    return;
  }
  if (t.tag === 'TMeta') {
    if (m === t) return;
    if (t.type) return subtypeTMeta(tvs, m, t.type, left);
    if (!subset(m.tvs, t.tvs))
      return terr(`subset failed: ${showType(m)} := ${showType(t)}`);
    m.type = t;
    return;
  }
  if (t.tag === 'TSkol') {
    if (!contains(m.tvs, t.id))
      return terr(`tvar out of scope: ${showType(m)} := ${showType(t)}`);
    m.type = t;
    return;
  }
  return terr(`subtype unexpected type: ${showType(m)} := ${showType(t)}`);
};

const subtype = (tvs, a, b) => {
  console.log(`subtype ${showType(a)} <: ${showType(b)}`);
  if (a === b) return;
  if (a.tag === 'TVar' && b.tag === 'TVar' && a.name === b.name) return;
  if (a.tag === 'TFun' && b.tag === 'TFun') {
    subtype(tvs, b.left, a.left);
    subtype(tvs, a.right, b.right);
    return;
  }
  if (b.tag === 'TForall') {
    const sk = freshTSkol();
    subtype(Cons(sk.id, tvs), a, openTForall(b, sk));
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
  return terr(`cannot synth ${showTerm(t)}`);
};

const check = (env, tvs, t, ty) => {
  console.log(`check ${showTerm(t)} : ${showType(ty)}`);
  if (ty.tag === 'TMeta' && ty.type) return check(env, tvs, t, ty.type);
  if (ty.tag === 'TForall') {
    const sk = freshTSkol();
    check(env, Cons(sk.id, tvs), t, openTForall(ty, sk));
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

const infer = (env, t) => {
  resetTMetaId();
  resetTSkolId();
  const ty = synth(env, Nil, t);
  return prune(ty);
};

// testing
const v = Var;
const tv = TVar;
const tid = TForall('t', TFun(tv('t'), tv('t')));

const env = fromArray([
  ['id', tid],
]);

const term = Ann(App(Abs('x', Abs('y', v('x'))), Abs('x', v('x'))), TForall('a', TForall('b', TFun(tv('a'), TFun(tv('b'), tv('b'))))));
console.log(showTerm(term));
const ty = infer(env, term);
console.log(showType(ty));
