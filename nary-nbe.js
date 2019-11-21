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

// either
const Left = val => ({ tag: 'Left', val });
const Right = val => ({ tag: 'Right', val });

const caseEither = (e, f, g) => e.tag === 'Left' ? f(e.val) : g(e.val);

// names
const nextName = x => {
  const s = x.split('$');
  if (s.length === 2) return `${s[0]}\$${+s[1] + 1}`;
  return `${x}\$0`;
};
const fresh = (xs, x) => {
  if (x === '_') return x;
  while (lookup(xs, x)) x = nextName(x);
  return x;
};

// terms
const Var = name => ({ tag: 'Var', name });
const Abs = (name, body) => ({ tag: 'Abs', name, body });
const App = (left, right) => ({ tag: 'App', left, right });
const Ann = (term, type) => ({ tag: 'Ann', term, type });

const abs = (vs, body) => vs.reduceRight((x, y) => Abs(y, x), body);
const appFrom = ts => ts.reduce(App);
function app() { return appFrom(Array.from(arguments)) }

const showTerm = t => {
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Abs')
    return `(\\${t.name}. ${showTerm(t.body)})`;
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
const TMeta = id => ({ tag: 'TMeta', id });
const TFun = (left, right) => ({ tag: 'TFun', left, right });
const TApp = (left, right) => ({ tag: 'TApp', left, right });
const TForall = (name, body) => ({ tag: 'TForall', name, body });

const tforall = (tvs, body) => tvs.reduceRight((b, x) => TForall(x, b), body);
const tfunFrom = ts => ts.reduceRight((x, y) => TFun(y, x));
function tfun() { return tfunFrom(Array.from(arguments)) }
const tappFrom = ts => ts.reduce(TApp);
function tapp() { return tappFrom(Array.from(arguments)) }

const showType = t => {
  if (t.tag === 'TVar') return t.name;
  if (t.tag === 'TMeta') return `?${t.id}`;
  if (t.tag === 'TFun') return `(${showType(t.left)} -> ${showType(t.right)})`;
  if (t.tag === 'TApp') return `(${showType(t.left)} ${showType(t.right)})`;
  if (t.tag === 'TForall') return `(forall ${t.name}. ${showType(t.body)})`;
};

// metas
const Unsolved = tvs => ({ tag: 'Unsolved', tvs });
const Solved = val => ({ tag: 'Solved', val });

let metas = [];

const resetMetas = () => { metas = [] };
const freshMeta = ts => {
  const id = metas.length;
  metas[id] = Unsolved(map(ts, x => x[0]));
  return TMeta(id);
};
const hasMeta = id => !!metas[id];
const getMeta = id => {
  const s = metas[id];
  if (!s) return terr(`meta ?${id} not found`);
  return s;
};
const setMeta = (id, val) => { metas[id] = Solved(val) };

// vals
const VFun = (left, right) => ({ tag: 'VFun', left, right });
const VApp = (left, right) => ({ tag: 'VApp', left, right });
const VForall = (name, body) => ({ tag: 'VForall', name, body });

const force = t => {
  while (t.tag === 'TMeta') {
    const v = getMeta(t.id);
    if (v.tag === 'Unsolved') break;
    t = v.val;
  }
  return t;
};

const eval = (vs, t) => {
  if (t.tag === 'TVar') {
    const r = lookup(vs, t.name);
    if (!r) return terr(`lookup ${t.name} failed in eval`);
    return r === true ? t : r;
  }
  if (t.tag === 'TMeta') return t;
  if (t.tag === 'TFun')
    return VFun(eval(vs, t.left), eval(vs, t.right));
  if (t.tag === 'TApp')
    return VApp(eval(vs, t.left), eval(vs, t.right));
  if (t.tag === 'TForall')
    return VForall(t.name, u => eval(Cons([t.name, u], vs), t.body));
  return terr('eval');
};
const quote = (vs, v_) => {
  const v = force(v_);
  if (v.tag === 'TVar') return v;
  if (v.tag === 'TMeta') return v;
  if (v.tag === 'VFun') return TFun(quote(vs, v.left), quote(vs, v.right));
  if (v.tag === 'VApp') return TApp(quote(vs, v.left), quote(vs, v.right));
  if (v.tag === 'VForall') {
    const x = fresh(vs, v.name);
    return TForall(x, quote(Cons([x, true], vs), v.body(TVar(x))));
  }
  return terr(`quote`);
};
const nf = (vs, t) => quote(vs, eval(vs, t));

// unification
const checkSolution = (id, xs, t) => {
  if (t.tag === 'TVar') {
    if (!contains(xs, t.name))
      return terr(`scope error`);
    return;
  }
  if (t.tag === 'TMeta') {
    if (t.id === id) return terr(`occurs check failed`);
    const s = getMeta(t.id);
    if (s.tag === 'Unsolved' && !subset(s.tvs, xs))
      return terr(`tvs not a subset`);
    return;
  }
  if (t.tag === 'TFun') {
    checkSolution(id, xs, t.left);
    checkSolution(id, xs, t.right);
    return;
  }
  if (t.tag === 'TApp') {
    checkSolution(id, xs, t.left);
    checkSolution(id, xs, t.right);
    return;
  }
  if (t.tag === 'TForall') {
    checkSolution(id, Cons(t.name, xs), t.body);
    return;
  }
};

const solve = (vs, id, t) => {
  const tvs = getMeta(id).tvs;
  const rhs = quote(vs, t);
  checkSolution(id, tvs, rhs);
  setMeta(id, t);
};

const unify = (vs, a_, b_) => {
  const a = force(a_);
  const b = force(b_);
  console.log(`unify ${showType(quote(vs, a))} ~ ${showType(quote(vs, b))}`);
  if (a.tag === 'TMeta' && b.tag === 'TMeta' && a.id === b.id) return;
  if (a.tag === 'TVar' && b.tag === 'TVar' && a.name === b.name) return;
  if (a.tag === 'VFun' && b.tag === 'VFun') {
    unify(vs, a.left, b.left);
    unify(vs, a.right, b.right);
    return;
  }
  if (a.tag === 'VApp' && b.tag === 'VApp') {
    unify(vs, a.left, b.left);
    unify(vs, a.right, b.right);
    return;
  }
  if (a.tag === 'VForall' && b.tag === 'VForall') {
    const x = fresh(vs, a.name);
    const vx = TVar(x);
    unify(Cons([x, true], vs), a.body(vx), b.body(vx));
    return;
  }
  if (a.tag === 'TMeta') return solve(vs, a.id, b);
  if (b.tag === 'TMeta') return solve(vs, b.id, a);
  return terr(`cannot unify ${showType(quote(vs, a))} ~ ${showType(quote(vs, b))}`);
};

// inference
const instantiate = (vs, ty_) => {
  const ty = force(ty_);
  if (ty.tag === 'VForall') {
    const m = freshMeta(vs);
    return instantiate(vs, ty.body(m));
  }
  return ty;
};

const check = (ts, vs, tm, ty_) => {
  const ty = force(ty_);
  console.log(`check ${showTerm(tm)} : ${showType(quote(vs, ty))}`);
  if (ty.tag === 'VForall') {
    const x = fresh(vs, ty.name);
    const vx = TVar(x);
    check(ts, Cons([ty.name, vx], vs), tm, ty.body(vx));
    return;
  }
  if (tm.tag === 'Abs' && ty.tag === 'VFun') {
    check(Cons([tm.name, ty.left], ts), vs, tm.body, ty.right);
    return;
  }
  if (tm.tag === 'App') {
    const [f, as] = flattenApp(tm);
    console.log(showTerm(f), '@', showList(as, showTerm));
    const ft = synth(ts, vs, f);
    const [rt, tas] = collect(vs, ft, as);
    const inst = instantiate(vs, rt);
    unify(vs, inst, ty);
    console.log(showType(quote(vs, rt)), showList(tas, ([tm, ty]) => `${showTerm(tm)} : ${showType(quote(vs, ty))}`));
    handleArgs(ts, vs, tas);
    return;
  }
  const ty2 = synth(ts, vs, tm);
  const inst = instantiate(vs, ty2);
  unify(vs, inst, ty);
};

const synth = (ts, vs, tm) => {
  console.log(`synth ${showTerm(tm)}`);
  if (tm.tag === 'Var') {
    const ty = lookup(ts, tm.name);
    if (!ty) return terr(`undefined var ${tm.name}`);
    return ty;
  }
  if (tm.tag === 'Abs') {
    const a = freshMeta(vs);
    const b = freshMeta(vs);
    check(Cons([tm.name, a], ts), vs, tm.body, b);
    return VFun(a, b);
  }
  if (tm.tag === 'App') {
    const [f, as] = flattenApp(tm);
    console.log(showTerm(f), '@', showList(as, showTerm));
    const ft = synth(ts, vs, f);
    const [rt, tas] = collect(vs, ft, as);
    console.log(showType(quote(vs, rt)), showList(tas, ([tm, ty]) => `${showTerm(tm)} : ${showType(quote(vs, ty))}`));
    handleArgs(ts, vs, tas);
    return rt;
  }
  if (tm.tag === 'Ann') {
    const vty = eval(vs, tm.type);
    check(ts, vs, tm.term, vty);
    return vty;
  }
};

const collect = (vs, ft_, as) => {
  const ft = force(ft_);
  if (as.tag === 'Nil') return [ft, Nil];
  if (ft.tag === 'VForall') {
    const m = freshMeta(vs);
    return collect(vs, ft.body(m), as);
  }
  if (ft.tag === 'VFun') {
    const [rt, ras] = collect(vs, ft.right, as.tail);
    return [rt, Cons([as.head, ft.left], ras)];
  }
  if (ft.tag === 'TMeta') {
    const a = freshMeta(vs);
    const b = freshMeta(vs);
    const fn = VFun(a, b);
    setMeta(ft.id, fn);
    return collect(vs, fn, as);
  }
  return terr(`cannot collect: ${showType(quote(vs, ft))} @ ${showList(as, showTerm)}`);
};

const handleArgs = (ts, vs, tas) => {
  let a = toArray(tas, ([tm, ty]) => [tm, force(ty)]);
  a = a.filter(([tm, ty]) => {
    const m = ty.tag === 'TMeta';
    if (!m) {
      check(ts, vs, tm, ty);
      return false;
    }
    return true;
  });
  a.forEach(([tm, ty]) => check(ts, vs, tm, ty));
};

const infer = (tm, ts = Nil, vs = Nil) => {
  const ty = synth(ts, vs, tm);
  return quote(vs, force(ty));
};

// testing
const v = Var;
const tv = TVar;

const List = t => tapp(tv('List'), t);
const tid = tforall(['t'], tfun(tv('t'), tv('t')));

const vs = fromArray([
  ['List', true],
]);
const ts = fromArray([
  ['id', eval(vs, tid)],
  ['const', eval(vs, tforall(['a', 'b'], tfun(tv('a'), tv('b'), tv('a'))))],
  ['app', eval(vs, tforall(['a', 'b'], tfun(tfun(tv('a'), tv('b')), tv('a'), tv('b'))))],
  ['rapp', eval(vs, tforall(['a', 'b'], tfun(tv('a'), tfun(tv('a'), tv('b')), tv('b'))))],
  ['Nil', eval(vs, tforall(['t'], List(tv('t'))))],
  ['Cons', eval(vs, tforall(['t'], tfun(tv('t'), List(tv('t')), List(tv('t')))))],
  ['rcons', eval(vs, tforall(['t'], tfun(List(tv('t')), tv('t'), List(tv('t')))))],
  ['ids', eval(vs, List(tid))]
]);

const tm = app(v('Cons'), v('id'), v('ids'));
console.log(showTerm(tm));
const ty = infer(tm, ts, vs);
console.log(showType(ty));
