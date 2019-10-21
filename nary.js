/*
  Simple implementation of type inference for invariant System F.
  Supports some impredicativity by first checking arguments that
  are not checked by a meta type variable.
  Also elaborates to System F.
  Does not do any generalization.

  TODO:
  - monomorphic flag in meta variable?
  - is skolem tv prune safe?
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
const map = (l, f) =>
  l.tag === 'Cons' ? Cons(f(l.head), map(l.tail, f)) : l;
const foldl = (f, v, l) =>
  l.tag === 'Cons' ? foldl(f, f(v, l.head), l.tail) : v;
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
const toArray = (l, m = x => x, f = () => true) => {
  const a = [];
  while (l.tag === 'Cons') {
    if (f(l.head)) a.push(m(l.head));
    l = l.tail;
  }
  return a;
};

// terms
const Var = name => ({ tag: 'Var', name });
const Abs = (name, body, type) => ({ tag: 'Abs', name, body, type });
const App = (left, right) => ({ tag: 'App', left, right });
const Ann = (term, type) => ({ tag: 'Ann', term, type });
const AbsT = (name, body) => ({ tag: 'AbsT', name, body });
const AppT = (left, right) => ({ tag: 'AppT', left, right });

const absT = (tvs, body) => tvs.reduceRight((x, y) => AbsT(y, x), body);

const showTerm = t => {
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Abs')
    return t.type ? `(\\(${t.name} : ${showType(t.type)}). ${showTerm(t.body)})` : `(\\${t.name}. ${showTerm(t.body)})`;
  if (t.tag === 'App')
    return `(${showTerm(t.left)} ${showTerm(t.right)})`;
  if (t.tag === 'Ann')
    return `(${showTerm(t.term)} : ${showType(t.type)})`;
  if (t.tag === 'AbsT') return `(/\\${t.name}. ${showTerm(t.body)})`;
  if (t.tag === 'AppT')
    return `(${showTerm(t.left)} @${showType(t.right)})`;
};

const flattenApp = t => {
  let r = Nil;
  while (t.tag === 'App') {
    r = Cons(t.right, r)
    t = t.left;
  }
  return [t, r];
};

const pruneTerm = t => {
  if (t.tag === 'Abs')
    return t.type ? Abs(t.name, pruneTerm(t.body), prune(t.type, true)) : t;
  if (t.tag === 'App') return App(pruneTerm(t.left), pruneTerm(t.right));
  if (t.tag === 'Ann') return Ann(pruneTerm(t.term), prune(t.type, true));
  if (t.tag === 'AbsT') return AbsT(t.name, pruneTerm(t.body));
  if (t.tag === 'AppT') return AppT(pruneTerm(t.left), prune(t.right, true));
  return t;
};

// types
const TVar = name => ({ tag: 'TVar', name });
const TForall = (name, body) => ({ tag: 'TForall', name, body });
const TApp = (left, right) => ({ tag: 'TApp', left, right });
const TMeta = (id, tvs) => ({ tag: 'TMeta', id, tvs, type: null });
const TSkol = (id, name) => ({ tag: 'TSkol', id, name });

const TFunC = TVar('->');
const TFun = (left, right) => TApp(TApp(TFunC, left), right);
const isTFun = t =>
  t.tag === 'TApp' && t.left.tag === 'TApp' && t.left.left === TFunC;
const matchTFun = t => isTFun(t) ? ({ left: t.left.right, right: t.right }) : null;

let _tmetaid = 0;
const resetTMetaId = () => { _tmetaid = 0 };
const freshTMeta = tvs => TMeta(_tmetaid++, tvs);

let _tskolid = 0;
const resetTSkolId = () => { _tskolid = 0 };
const freshTSkol = name => TSkol(_tskolid++, name);

const tforall = (tvs, body) => tvs.reduceRight((x, y) => TForall(y, x), body);

const showType = t => {
  if (t.tag === 'TVar') return t.name;
  if (t.tag === 'TMeta')
    return `?${t.id}${showList(t.tvs)}${t.type ? `{${showType(t.type)}}` : ''}`;
  if (t.tag === 'TSkol') return `'${t.name}\$${t.id}`;
  if (t.tag === 'TForall')
    return `(forall ${t.name}. ${showType(t.body)})`;
  const m = matchTFun(t);
  if (m) return `(${showType(m.left)} -> ${showType(m.right)})`;
  if (t.tag === 'TApp')
    return `(${showType(t.left)} ${showType(t.right)})`;
};

const force = t => {
  while (t.tag === 'TMeta' && t.type) t = t.type;
  return t;
};
const prune = (t, forceTSkol) => {
  if (t.tag === 'TMeta') return t.type ? t.type = prune(t.type, forceTSkol) : t;
  if (t.tag === 'TApp') return TApp(prune(t.left, forceTSkol), prune(t.right, forceTSkol));
  if (t.tag === 'TForall') return TForall(t.name, prune(t.body, forceTSkol));
  if (t.tag === 'TSkol') return forceTSkol ? TVar(t.name) : t;
  return t;
};

const substTVar = (x, s, t) => {
  if (t.tag === 'TVar') return t.name === x ? s : t;
  if (t.tag === 'TMeta' && t.type) return substTVar(x, s, t.type);
  if (t.tag === 'TApp')
    return TApp(substTVar(x, s, t.left), substTVar(x, s, t.right));
  if (t.tag === 'TForall')
    return t.name === x ? t : TForall(t.name, substTVar(x, s, t.body));
  return t;
};
const openTForall = (f, t) => substTVar(f.name, t, f.body);

const isMono = t => {
  if (t.tag === 'TMeta') return t.type ? isMono(t.type) : true;
  if (t.tag === 'TForall') return false;
  if (t.tag === 'TApp') return isMono(t.left) && isMono(t.right);
  return true;
};

const tmetas = (t_, a = []) => {
  const t = force(t_);
  if (t.tag === 'TMeta') {
    if (a.indexOf(t) < 0) a.push(t);
    return a;
  }
  if (t.tag === 'TForall') return tmetas(t.body, a);
  if (t.tag === 'TApp') return tmetas(t.right, tmetas(t.left, a));
  return a;
};

// unification
const checkSolution = (m, t) => {
  if (t === m) return false;
  if (t.tag === 'TMeta')
    return subset(m.tvs, t.tvs) && subset(t.tvs, m.tvs);
  if (t.tag === 'TApp')
    return checkSolution(m, t.left) && checkSolution(m, t.right);
  if (t.tag === 'TForall')
    return checkSolution(m, t.body);
  if (t.tag === 'TSkol') return contains(m.tvs, t.id);
  return true;
};
const solve = (m, t_) => {
  // console.log(`solve ${showType(m)} := ${showType(t)}`);
  const t = prune(t_);
  if (!checkSolution(m, t))
    return terr(`solve failed: ${showType(m)} := ${showType(t)}`);
  m.type = t;
};
const unify = (a_, b_) => {
  // console.log(`unify ${showType(a_)} ~ ${showType(b_)}`);
  if (a_ === b_) return;
  const a = force(a_);
  const b = force(b_);
  if (a === b) return;
  if (a.tag === 'TVar' && b.tag === 'TVar' && a.name === b.name) return;
  if (a.tag === 'TApp' && b.tag === 'TApp') {
    unify(a.left, b.left);
    unify(a.right, b.right);
    return;
  }
  if (a.tag === 'TForall' && b.tag === 'TForall') {
    const sk = freshTSkol(a.name);
    unify(openTForall(a, sk), openTForall(b, sk));
    return;
  }
  if (a.tag === 'TMeta') return solve(a, b);
  if (b.tag === 'TMeta') return solve(b, a)
  return terr(`failed ${showType(a)} ~ ${showType(b)}`);
};

// inference
const instantiate = (tvs, ty_) => {
  const ty = force(ty_);
  if (ty.tag === 'TForall') {
    const m = freshTMeta(tvs);
    const [rty, args] = instantiate(tvs, openTForall(ty, m));
    return [rty, Cons(m, args)];
  }
  return [ty, Nil];
};

const check = (env, tvs, t, ty_) => {
  // console.log(`check ${showTerm(t)} : ${showType(ty_)}`);
  const ty = force(ty_);
  if (ty.tag === 'TForall') {
    const sk = freshTSkol(ty.name);
    const tm = check(env, Cons(sk.id, tvs), t, openTForall(ty, sk));
    return AbsT(ty.name, tm);
  }
  const m = matchTFun(ty);
  if (t.tag === 'Abs' && !t.type && m) {
    const tm = check(Cons([t.name, m.left], env), tvs, t.body, m.right);
    return Abs(t.name, tm, m.left);
  }
  if (t.tag === 'App') {
    const [fn, args] = flattenApp(t);
    const [fty, ftm] = synth(env, tvs, fn);
    const [rt, targs] = collect(tvs, fty, args);
    const [inst, margs] = instantiate(tvs, rt);
    unify(inst, ty);
    // console.log(`${showList(targs, ([b, t, ty]) => b ? `@${showType(t)}` : `${showTerm(t)} : ${showType(ty)}`)} => ${showType(rt)}`);
    handleArgs(env, tvs, targs);
    const tm = foldl((acc, [b, t, ty]) => b ? AppT(acc, t) : App(acc, check(env, tvs, t, ty)), ftm, targs);
    return foldl((a, m) => AppT(a, m), tm, margs);
  }
  const [inf, tm] = synth(env, tvs, t);
  const [inst, args] = instantiate(tvs, inf);
  unify(inst, ty);
  return foldl((a, m) => AppT(a, m), tm, args);
};

const synth = (env, tvs, t) => {
  // console.log(`synth ${showTerm(t)}`);
  if (t.tag === 'Var') {
    const ty = lookup(env, t.name);
    if (!ty) return terr(`undefined var ${t.name}`);
    return [ty, t];
  }
  if (t.tag === 'Ann') {
    const tm = check(env, tvs, t.term, t.type);
    return [t.type, tm];
  }
  if (t.tag === 'App') {
    const [fn, args] = flattenApp(t);
    const [ty, ftm] = synth(env, tvs, fn);
    const [rt, targs] = collect(tvs, ty, args);
    // console.log(`${showList(targs, ([b, t, ty]) => b ? `@${showType(t)}` : `${showTerm(t)} : ${showType(ty)}`)} => ${showType(rt)}`);
    handleArgs(env, tvs, targs);
    const result = foldl((acc, [b, t, ty]) => b ? AppT(acc, t) : App(acc, check(env, tvs, t, ty)), ftm, targs);
    return [rt, result];
  }
  if (t.tag === 'Abs') {
    if (t.type) {
      const rt = freshTMeta(tvs);
      const tm = check(Cons([t.name, t.type], env), tvs, t.body, rt);
      return [TFun(t.type, rt), Abs(t.name, tm, t.type)];
    } else {
      const a = freshTMeta(tvs);
      const b = freshTMeta(tvs);
      const tm = check(Cons([t.name, a], env), tvs, t.body, b);
      // question: is this monomorphic check needed/enough?
      /*
      if (!isMono(a))
        return terr(`polymorphic type inferred for parameter of ${showTerm(t)}: ${showType(a)}`);
      */
      return [TFun(a, b), Abs(t.name, tm, a)];
    }
  }
  if (t.tag === 'AbsT') {
    const sk = freshTSkol(t.name);
    const ntvs = Cons(sk, tvs);
    const m = freshTMeta(ntvs);
    const tm = check(env, ntvs, t.body, m);
    return [TForall(t.name, m), AbsT(t.name, tm)];
  }
  if (t.tag === 'AppT') {
    const [ty, tm] = synth(env, tvs, t.left);
    return synthappT(tm, ty, t.right);
  }
  return terr(`cannot synth ${showTerm(t)}`);
};

const collect = (tvs, ty_, args) => {
  const ty = force(ty_);
  if (args.tag === 'Nil') return [ty, Nil]
  if (ty.tag === 'TForall') {
    const m = freshTMeta(tvs);
    const [rt, rest] = collect(tvs, openTForall(ty, m), args);
    return [rt, Cons([true, m], rest)];
  }
  const m = matchTFun(ty);
  if (m) {
    const [rt, rest] = collect(tvs, m.right, args.tail);
    return [rt, Cons([false, args.head, m.left], rest)];
  }
  if (ty.tag === 'TMeta') {
    const a = freshTMeta(ty.tvs);
    const b = freshTMeta(ty.tvs);
    const fun = TFun(a, b)
    ty.type = fun;
    return collect(tvs, fun, args);
  }
  return terr(`cannot collect ${showType(ty)} @ ${showList(args, showTerm)}`);
};

const handleArgs = (env, tvs, targs_) => {
  const a = toArray(targs_, ([_, t, ty]) => [t, ty] , ([b]) => !b);
  // first pass for guarded arguments
  for (let i = 0; i < a.length; i++) {
    const [tm, ty] = a[i];
    const fty = force(ty);
    if (fty.tag !== 'TMeta') {
      check(env, tvs, tm, fty);
      a.splice(i, 1);
      i--;
    }
  }
  // second pass for the rest
  for (let i = 0; i < a.length; i++) {
    const [tm, ty] = a[i];
    check(env, tvs, tm, ty);
  }
};

const synthappT = (tm, ty_, type) => {
  const ty = force(ty_);
  if (ty.tag === 'TForall') return [openTForall(ty, type), AppT(tm, type)];
  return terr(`not a forall in type application: ${showType(ty)} @ ${showType(type)}`);
};

const infer = (env, t, gen = false) => {
  resetTMetaId();
  resetTSkolId();
  const [ty, tm] = synth(env, Nil, t);
  const tms = tmetas(ty);
  if (gen) {
    let id = 0;
    const tvs = tms.map(m => {
      const tv = `\$${id++}`;
      m.type = TVar(tv);
      return tv;
    });
    return [tforall(tvs, prune(ty)), absT(tvs, pruneTerm(tm))];
  } else {
    if (tms.length > 0)
      return terr(`unsolved tmetas in type: ${showType(prune(ty))}`);
    return [prune(ty), pruneTerm(tm)];
  }
};

// testing
const v = Var;
const tv = TVar;
function tfun() { return Array.from(arguments).reduceRight((x, y) => TFun(y, x)) }
function app() { return Array.from(arguments).reduce(App) }
const tid = TForall('t', tfun(tv('t'), tv('t')));
const List = t => TApp(tv('List'), t);
const ST = (s, t) => TApp(TApp(tv('ST'), s), t);
const Pair = (a, b) => TApp(TApp(tv('Pair'), a), b);

const env = fromArray([
  ['head', TForall('t', TFun(List(tv('t')), tv('t')))],
  ['tail', TForall('t', TFun(List(tv('t')), List(tv('t'))))],
  ['Nil', TForall('t', List(tv('t')))],
  ['Cons', TForall('t', TFun(tv('t'), TFun(List(tv('t')), List(tv('t')))))],
  ['single', TForall('t', TFun(tv('t'), List(tv('t'))))],
  ['append', TForall('t', TFun(List(tv('t')), TFun(List(tv('t')), List(tv('t')))))],
  ['length', TForall('t', TFun(List(tv('t')), tv('Int')))],
  ['runST', TForall('t', TFun(TForall('s', ST(tv('s'), tv('t'))), tv('t')))],
  ['argST', TForall('s', ST(tv('s'), tv('Int')))],
  ['pair', TForall('a', TForall('b', TFun(tv('a'), TFun(tv('b'), Pair(tv('a'), tv('b'))))))],
  ['pair2', TForall('b', TForall('a', TFun(tv('a'), TFun(tv('b'), Pair(tv('a'), tv('b'))))))],
  ['id', tid],
  ['const', tforall(['a', 'b'], TFun(tv('a'), TFun(tv('b'), tv('a'))))],
  ['ids', List(tid)],
  ['inc', TFun(tv('Int'), tv('Int'))],
  ['choose', TForall('t', TFun(tv('t'), TFun(tv('t'), tv('t'))))],
  ['poly', TFun(tid, Pair(tv('Int'), tv('Bool')))],
  ['auto', TFun(tid, tid)],
  ['auto2', TForall('b', TFun(tid, TFun(tv('b'), tv('b'))))],
  ['map', TForall('a', TForall('b', TFun(TFun(tv('a'), tv('b')), TFun(List(tv('a')), List(tv('b'))))))],
  ['app', TForall('a', TForall('b', TFun(TFun(tv('a'), tv('b')), TFun(tv('a'), tv('b')))))],
  ['revapp', TForall('a', TForall('b', TFun(tv('a'), TFun(TFun(tv('a'), tv('b')), tv('b')))))],
  ['f', TForall('t', TFun(TFun(tv('t'), tv('t')), TFun(List(tv('t')), tv('t'))))],
  ['g', TForall('t', TFun(List(tv('t')), TFun(List(tv('t')), tv('t'))))],
  ['k', TForall('t', TFun(tv('t'), TFun(List(tv('t')), tv('t'))))],
  ['h', TFun(tv('Int'), tid)],
  ['l', List(TForall('t', TFun(tv('Int'), TFun(tv('t'), tv('t')))))],
  ['r', TFun(TForall('a', TFun(tv('a'), tid)), tv('Int'))],
  ['str', tv('Str')],
  ['int', tv('Int')],
]);

let failed = 0;
[
  // A
  Abs('x', Abs('y', v('x'))),
  App(v('choose'), v('id')),
  Ann(App(v('choose'), v('id')), TFun(tid, tid)),
  App(App(v('choose'), v('Nil')), v('ids')),
  App(v('id'), v('auto')),
  App(v('id'), v('auto2')),
  App(App(v('choose'), v('id')), v('auto')),
  App(App(v('choose'), v('id')), v('auto2')), // X
  App(App(v('f'), App(v('choose'), v('id'))), v('ids')), // X
  App(App(v('f'), Ann(App(v('choose'), v('id')), TFun(tid, tid))), v('ids')),
  App(v('poly'), v('id')),
  App(v('poly'), Abs('x', v('x'))),
  App(App(v('id'), v('poly')), Abs('x', v('x'))),

  // C
  App(v('length'), v('ids')),
  App(v('tail'), v('ids')),
  App(v('head'), v('ids')),
  App(v('single'), v('id')),
  Ann(App(v('single'), v('id')), List(tid)),
  App(App(v('Cons'), v('id')), v('ids')),
  App(App(v('Cons'), Abs('x', v('x'))), v('ids')),
  App(App(v('append'), App(v('single'), v('inc'))), App(v('single'), v('id'))),
  App(App(v('g'), App(v('single'), v('id'))), v('ids')), // X
  App(App(v('g'), Ann(App(v('single'), v('id')), List(tid))), v('ids')),  
  App(App(v('map'), v('poly')), App(v('single'), v('id'))),
  App(App(v('map'), v('head')), App(v('single'), v('ids'))),

  // D
  App(App(v('app'), v('poly')), v('id')),
  App(App(v('revapp'), v('id')), v('poly')),
  App(v('runST'), v('argST')),
  App(App(v('app'), v('runST')), v('argST')),
  App(App(v('revapp'), v('argST')), v('runST')),

  // E
  App(App(v('k'), v('h')), v('l')), // X
  App(App(v('k'), Abs('x', App(v('h'), v('x')))), v('l')),
  App(v('r'), Abs('x', Abs('y', v('y')))),

  // Other
  AbsT('t', Abs('x', v('x'), tv('t'))),
  AbsT('t', AppT(AbsT('t', Abs('x', v('x'), tv('t'))), tv('t'))),
  App(Abs('x', v('x')), Abs('x', v('x'))),
  Ann(Abs('x', Abs('y', v('x'))), TForall('a', TFun(tv('a'), TForall('b', TFun(tv('b'), tv('a')))))),
  App(App(Ann(Abs('x', Abs('y', v('x'))), TForall('a', TFun(tv('a'), TForall('b', TFun(tv('b'), tv('a')))))), v('int')), v('str')),
  App(v('id'), Abs('x', v('x'))),
  App(v('const'), v('id')),
  Ann(App(v('const'), v('id')), tforall(['a', 'b'], TFun(tv('a'), TFun(tv('b'), tv('b'))))),
  Ann(App(v('const'), v('id')), tforall(['a'], TFun(tv('a'), tid))),
  App(v('const'), Abs('x', v('x'))),
  Ann(App(v('const'), Abs('x', v('x'))), tforall(['a', 'b'], TFun(tv('a'), TFun(tv('b'), tv('b'))))),
  Ann(App(v('const'), Abs('x', v('x'))), tforall(['a'], TFun(tv('a'), tid))),
].forEach(t => {
  try {
    const [ty, tm] = infer(env, t, true);
    console.log(`${showTerm(t)}\n: ${showType(ty)}\n=> ${showTerm(tm)}\n`);
  } catch(e) {
    failed++;
    console.log(`${showTerm(t)}\n=> ${e}\n`);
  }
});
console.log(`failed: ${failed}`);
