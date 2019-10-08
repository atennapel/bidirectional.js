/*
  Simple implementation of type inference for invariant System F.
  Supports some impredicativity.
*/
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

const each = (l, f) => {
  while (l.tag === 'Cons') {
    f(l.head);
    l = l.tail;
  }
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

const flattenApp = t => {
  let r = Nil;
  while (t.tag === 'App') {
    r = Cons(t.right, r)
    t = t.left;
  }
  return [t, r];
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

// unification
const checkSolution = (m, t) => {
  if (t === m) return false;
  if (t.tag === 'TMeta') {
    if (t.type) return checkSolution(m, t.type);
    return subset(m.tvs, t.tvs) && subset(t.tvs, m.tvs);
  }
  if (t.tag === 'TFun')
    return checkSolution(m, t.left) && checkSolution(m, t.right);
  if (t.tag === 'TForall')
    return checkSolution(m, t.body);
  if (t.tag === 'TSkol') return contains(m.tvs, t.id);
  return true;
};
const solve = (m, t) => {
  console.log(`solve ${showType(m)} := ${showType(t)}`);
  if (m === t) return;
  if (m.type) return unify(m.type, t);
  if (t.tag === 'TMeta' && t.type) return solve(m, t.type);
  if (!checkSolution(m, t))
    return terr(`solve failed: ${showType(m)} := ${showType(t)}`);
  m.type = t;
};
const unify = (a, b) => {
  console.log(`unify ${showType(a)} ~ ${showType(b)}`);
  if (a === b) return;
  if (a.tag === 'TVar' && b.tag === 'TVar' && a.name === b.name) return;
  if (a.tag === 'TFun' && b.tag === 'TFun') {
    unify(a.left, b.left);
    unify(a.right, b.right);
    return;
  }
  if (a.tag === 'TForall' && b.tag === 'TForall') {
    const sk = freshTSkol();
    unify(openTForall(a, sk), openTForall(b, sk));
    return;
  }
  if (a.tag === 'TMeta') return solve(a, b);
  if (b.tag === 'TMeta') return solve(b, a)
  return terr(`failed ${showType(a)} ~ ${showType(b)}`);
};
const subsume = (tvs, a, b) => {
  console.log(`subsume ${showType(a)} <: ${showType(b)}`);
  if (b.tag === 'TForall') {
    const sk = freshTSkol();
    return subsume(Cons(sk.id, tvs), a, openTForall(b, sk));
  }
  if (a.tag === 'TForall') {
    const m = freshTMeta(tvs);
    return subsume(tvs, openTForall(a, m), b);
  }
  return unify(a, b);
};

// inference
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
    const [fn, args] = flattenApp(t);
    const fty = synth(env, tvs, fn);
    const [rt, targs] = collect(tvs, fty, args);
    unify(rt, ty); // or subsume??
    console.log(`${showList(targs, ([t, ty]) => `${showTerm(t)} : ${showType(ty)}`)} -> ${showType(rt)} : ${showType(ty)}`);
    each(targs, ([t, ty]) => check(env, tvs, t, ty));
    return;
  }
  const inf = synth(env, tvs, t);
  subsume(tvs, inf, ty);
};

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
    const [fn, args] = flattenApp(t);
    const ty = synth(env, tvs, fn);
    const [rt, targs] = collect(tvs, ty, args);
    console.log(`${showList(targs, ([t, ty]) => `${showTerm(t)} : ${showType(ty)}`)} -> ${showType(rt)}`);
    each(targs, ([t, ty]) => check(env, tvs, t, ty));
    return rt;
  }
  if (t.tag === 'Abs') {
    const a = freshTMeta(tvs);
    const b = freshTMeta(tvs);
    check(Cons([t.name, a], env), tvs, t.body, b);
    return TFun(a, b);
  }
  return terr(`cannot synth ${showTerm(t)}`);
};

const collect = (tvs, ty, args) => {
  if (args.tag === 'Nil') return [ty, Nil]
  if (ty.tag === 'TForall') {
    const m = freshTMeta(tvs);
    return collect(tvs, openTForall(ty, m), args);
  }
  if (ty.tag === 'TFun') {
    const [rt, rest] = collect(tvs, ty.right, args.tail);
    return [rt, Cons([args.head, ty.left], rest)];
  }
  if (ty.tag === 'TMeta') {
    if (ty.type) return collect(tvs, ty.type, args);
    const a = freshTMeta(ty.tvs);
    const b = freshTMeta(ty.tvs);
    const fun = TFun(a, b)
    ty.type = fun;
    return collect(tvs, fun, args);
  }
  return terr(`cannot collect ${showType(ty)} @ ${showList(args, showTerm)}`);
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
function tfun() { return Array.from(arguments).reduceRight((x, y) => TFun(y, x)) }
function app() { return Array.from(arguments).reduce(App) }
const tid = TForall('t', tfun(tv('t'), tv('t')));

const env = fromArray([
  ['id', tid],
  ['ids', tfun(tv('U'), tid)],
  ['cons', TForall('t', tfun(tv('t'), tfun(tv('U'), tv('t')), tfun(tv('U'), tv('t'))))],
  ['snoc', TForall('t', tfun(tfun(tv('U'), tv('t')), tv('t'), tfun(tv('U'), tv('t'))))],
]);

const term = Ann(app(v('cons'), v('id'), v('ids')), tfun(tv('U'), tid));
console.log(showTerm(term));
const ty = infer(env, term);
console.log(showType(ty));
