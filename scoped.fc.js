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
const TApp = (left, right) => ({ tag: 'TApp', left, right });
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
  if (t.tag === 'TApp')
    return `(${showType(t.left)} ${showType(t.right)})`;
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

// subtyping
const checkSolution = (m, t) => {
  if (t === m) return false;
  if (t.tag === 'TMeta') {
    if (t.type) return checkSolution(m, t.type);
    return subset(m.tvs, t.tvs);
  }
  if (t.tag === 'TFun')
    return checkSolution(m, t.left) && checkSolution(m, t.right);
  if (t.tag === 'TApp')
    return checkSolution(m, t.left) && checkSolution(m, t.right);
  if (t.tag === 'TForall') return checkSolution(m, t.body);
  if (t.tag === 'TSkol') return contains(m.tvs, t.id);
  return true;
};
const unifyTMeta = (tvs, m, t) => {
  console.log(`unifyTMeta ${showType(m)} := ${showType(t)}`);
  if (m === t) return;
  if (m.type) return unify(tvs, m.type, t);
  if (t.tag === 'TMeta' && t.type) return unifyTMeta(tvs, m, t.type);
  if (!checkSolution(m, t))
    return terr(`unifyTMeta failed: ${showType(m)} := ${showType(t)}`);
  m.type = t;
};

const unify = (tvs, a, b) => {
  console.log(`unify ${showType(a)} ~ ${showType(b)}`);
  if (a === b) return;
  if (a.tag === 'TVar' && b.tag === 'TVar' && a.name === b.name) return;
  if (a.tag === 'TFun' && b.tag === 'TFun') {
    unify(tvs, a.left, b.left);
    unify(tvs, a.right, b.right);
    return;
  }
  if (a.tag === 'TApp' && b.tag === 'TApp') {
    unify(tvs, a.left, b.left);
    unify(tvs, a.right, b.right);
    return;
  }
  if (a.tag === 'TForall' && b.tag === 'TForall') {
    const sk = freshTSkol();
    unify(Cons(sk.id, tvs), openTForall(a, sk), openTForall(b, sk));
    return;
  }
  if (a.tag === 'TMeta') return unifyTMeta(tvs, a, b);
  if (b.tag === 'TMeta') return unifyTMeta(tvs, b, a);
  return terr(`failed ${showType(a)} ~ ${showType(b)}`);
};
const subsume = (tvs, a, b) => {
  if (b.tag === 'TForall') {
    const sk = freshTSkol();
    return unify(Cons(sk.id, tvs), a, openTForall(b, sk));
  }
  if (a.tag === 'TForall') {
    const m = freshTMeta(tvs);
    return unify(tvs, openTForall(a, m), b);
  }
  return unify(tvs, a, b);
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
    // TODO: check for that argument is monomorphic
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
  if (t.tag === 'App') {
    const fty = synth(env, tvs, t.left);
    return synthapp(env, tvs, fty, t.right, ty);
  }
  const inf = synth(env, tvs, t);
  subsume(tvs, inf, ty);
};

const synthapp = (env, tvs, ty, t, ety) => {
  console.log(`synthapp ${showType(ty)} @ ${showTerm(t)}${ety ? ` : ${showType(ety)}` : ''}`);
  // TOOD: N-ary applications
  if (ty.tag === 'TForall') {
    const m = freshTMeta(tvs);
    return synthapp(env, tvs, openTForall(ty, m), t, ety);
  }
  if (ty.tag === 'TFun') {
    if (ety) unify(tvs, ty.right, ety);
    check(env, tvs, t, ty.left);
    return ty.right;
  }
  if (ty.tag === 'TMeta') {
    if (ty.type) return synthapp(env, tvs, ty.type, t, ety);
    const a = freshTMeta(ty.tvs);
    const b = freshTMeta(ty.tvs);
    ty.type = TFun(a, b);
    if (ety) unify(tvs, b, ety);
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
  ['single', TForall('t', TFun(tv('t'), TApp(tv('List'), tv('t'))))],
]);

const term = Ann(App(v('single'), v('id')), TApp(tv('List'), tid));
console.log(showTerm(term));
const ty = infer(env, term);
console.log(showType(ty));
