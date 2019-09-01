/**
 * This is a minimal implementation of a bidirectional version of HMF
 * invariant but impredicative instantiations are supported
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

const flattenApp = t => {
  const args = [];
  while (t.tag === 'App') {
    args.push(t.right);
    t = t.left;
  }
  return [t, args.reverse()];
};

// types
const TVar = name => ({ tag: 'TVar', name });
const TForall = (name, body) => ({ tag: 'TForall', name, body });
const TFun = (left, right) => ({ tag: 'TFun', left, right });
const TApp = (left, right) => ({ tag: 'TApp', left, right });
const TMeta = (id, tvs, mono) => ({ tag: 'TMeta', id, tvs, type: null, mono });
const TSkol = id => ({ tag: 'TSkol', id });

let _tmetaid = 0;
const resetTMetaId = () => { _tmetaid = 0 };
const freshTMeta = (tvs, mono = false) => TMeta(_tmetaid++, tvs, mono);

let _tskolid = 0;
const resetTSkolId = () => { _tskolid = 0 };
const freshTSkol = () => TSkol(_tskolid++);

const showType = t => {
  if (t.tag === 'TVar') return t.name;
  if (t.tag === 'TMeta')
    return `?${t.mono ? '`' : ''}${t.id}${showList(t.tvs)}${t.type ? `{${showType(t.type)}}` : ''}`;
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
    if (m.mono) t.mono = true;
    if (t.type) return checkSolution(m, t.type);
    return subset(m.tvs, t.tvs);
  }
  if (t.tag === 'TFun')
    return checkSolution(m, t.left) && checkSolution(m, t.right);
  if (t.tag === 'TApp')
    return checkSolution(m, t.left) && checkSolution(m, t.right);
  if (t.tag === 'TForall') {
    if (m.mono) return false;
    return checkSolution(m, t.body);
  }
  if (t.tag === 'TSkol') return contains(m.tvs, t.id);
  return true;
};
const unifyTMeta = (tvs, m, t) => {
  //console.log(`unifyTMeta ${showType(m)} := ${showType(t)}`);
  if (m === t) return;
  if (m.type) return unify(tvs, m.type, t);
  if (t.tag === 'TMeta' && t.type) return unifyTMeta(tvs, m, t.type);
  if (!checkSolution(m, t))
    return terr(`unifyTMeta failed: ${showType(m)} := ${showType(t)}`);
  m.type = t;
};

const unify = (tvs, a, b) => {
  //console.log(`unify ${showType(a)} ~ ${showType(b)}`);
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
  //console.log(`subsume ${showType(a)} <: ${showType(b)}`);
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
  //console.log(`synth ${showTerm(t)}`);
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
    const [f, as] = flattenApp(t);
    const ty = synth(env, tvs, f);
    return synthapps(env, tvs, ty, as);
  }
  if (t.tag === 'Abs') {
    const a = freshTMeta(tvs, true);
    const b = freshTMeta(tvs);
    check(Cons([t.name, a], env), tvs, t.body, b);
    return TFun(a, b);
  }
  return terr(`cannot synth ${showTerm(t)}`);
};

const check = (env, tvs, t, ty) => {
  //console.log(`check ${showTerm(t)} : ${showType(ty)}`);
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
    const [f, as] = flattenApp(t);
    const fty = synth(env, tvs, f);
    return synthapps(env, tvs, fty, as, ty);
  }
  const inf = synth(env, tvs, t);
  subsume(tvs, inf, ty);
};

const synthapps = (env, tvs, ty, as, ety, acc = []) => {
  //console.log(`synthapps ${showType(ty)} @ [${as.map(showTerm).join(', ')}][${acc.map(([t, ty]) => `${showTerm(t)} : ${showType(ty)}`).join(', ')}]${ety ? ` : ${showType(ety)}` : ''}`);
  if (ty.tag === 'TForall') {
    const m = freshTMeta(tvs);
    return synthapps(env, tvs, openTForall(ty, m), as, ety, acc);
  }
  if (as.length > 0) {
    if (ty.tag === 'TFun') {
      const tm = as.shift();
      acc.push([tm, ty.left]);
      return synthapps(env, tvs, ty.right, as, ety, acc);
    }
    if (ty.tag === 'TMeta') {
      if (ty.type) return synthapps(env, tvs, ty.type, as, ety, acc);
      const a = freshTMeta(ty.tvs);
      const b = freshTMeta(ty.tvs);
      ty.type = TFun(a, b);
      const tm = as.shift();
      acc.push([tm, a]);
      return synthapps(env, tvs, b, as, ety, acc);
    }
    return terr(`synthapps failed, not a function type: ${showType(ty)}`);
  }
  if (ety) unify(tvs, ty, ety);
  while(acc.length > 0) {
    const [tm, tmty] = pickArg(acc);
    check(env, tvs, tm, tmty);
  }
  return ty;
};
const pickArg = acc => {
  for (let i = 0, l = acc.length; i < l; i++) {
    const opt = acc[i];
    if (prune(opt[1]).tag !== 'TMeta') {
      acc.splice(i, 1);
      return opt;
    }
  }
  return acc.shift();
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
]);

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

  // B

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
].forEach(t => {
  try {
    const ty = infer(env, t);
    console.log(`${showTerm(t)} : ${showType(ty)}`);
  } catch(e) {
    console.log(`${showTerm(t)} => ${e}`);
  }
});
