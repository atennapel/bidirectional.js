/**
 * This implementation uses the subtyping judgments from:
 * Formalization of a Polymorphic Subtyping Algorithm
 */

// util
const terr = msg => { throw new TypeError(msg) };

// names
let id = 0;
const freshId = () => id++;
const resetId = () => { id = 0 };

// types
const TCon = name => ({ tag: 'TCon', name });
const TVar = name => ({ tag: 'TVar', name });
const TMeta = () => ({ tag: 'TMeta', id: freshId(), type: null });
const TFun = (left, right) => ({ tag: 'TFun', left, right });
const TForall = (name, type) => ({ tag: 'TForall', name, type });

const tforall = (tvs, type) =>
  tvs.length === 0 ? type :
  tvs.reduceRight((t, n) => TForall(n, t), type);

const showTypeR = t => {
  if (t.tag === 'TCon') return t.name;
  if (t.tag === 'TVar') return t.name;
  if (t.tag === 'TMeta') return `?${t.id}`;
  if (t.tag === 'TFun')
    return `(${showTypeR(t.left)} -> ${showTypeR(t.right)})`;
  if (t.tag === 'TForall')
    return `(forall ${showTypeR(t.name)}. ${showTypeR(t.type)})`;
};

const prune = t => {
  if (t.tag === 'TMeta')
    return t.type ? (t.type = prune(t.type)) : t;
  if (t.tag === 'TFun')
    return TFun(prune(t.left), prune(t.right));
  if (t.tag === 'TForall')
    return TForall(t.name, prune(t.type));
  return t;
};
const showType = t => showTypeR(prune(t));

const substTVar = (x, s, t) => {
  if (x === t) return s;
  if (t.tag === 'TMeta' && t.type) return substTVar(x, s, t.type);
  if (t.tag === 'TFun')
    return TFun(substTVar(x, s, t.left), substTVar(x, s, t.right));
  if (t.tag === 'TForall')
    return t.name === x ? t : TForall(t.name, substTVar(x, s, t.type));
  return t;
};
const openTForall = (t, tf) => substTVar(tf.name, t, tf.type);

const hasTMeta = (x, t) => {
  if (x === t) return true;
  if (t.tag === 'TMeta' && t.type) return hasTMeta(x, t.type);
  if (t.tag === 'TFun')
    return hasTMeta(x, t.left) || hasTMeta(x, t.right);
  if (t.tag === 'TForall') return hasTMeta(x, t.type);
  return false;
};

const tmetas = (t, tms, res = []) => {
  if (t.tag === 'TMeta') {
    if (t.type) return tmetas(t.type, tms, res);
    if (tms.indexOf(t) >= 0 && res.indexOf(t) < 0) res.push(t);
    return res;
  }
  if (t.tag === 'TFun')
    return tmetas(t.right, tms, tmetas(t.left, tms, res));
  if (t.tag === 'TForall') return tmetas(t.type, tms, res);
  return res;
};

// dependency list
const Marker = () => ({ tag: 'Marker', id: freshId() });
const showElem = e => e.tag === 'Marker' ? `|>${e.id}` : showTypeR(e);

const deplist = [];
const remove = i => deplist.splice(i, 1);
const replace = (i, a) => deplist.splice(i, 1, ...a);
const indexOf = x => {
  for (let i = deplist.length - 1; i >= 0; i--)
    if (deplist[i] === x) return i;
  return -1;
};
const drop = m => deplist.splice(indexOf(m), deplist.length);

const showDeps = () => `[${deplist.map(showElem).join(', ')}]`;

// subsumption
const solve = (x, i, t) => {
  remove(i);
  x.type = t;
};
const subsumeTMeta = (x, t, right) => {
  console.log(`subsumeTMeta ${right ? `${showTypeR(t)} =: ${showTypeR(x)}` : `${showTypeR(x)} := ${showTypeR(t)}`}`);
  if (x.type) return right ? subsume(t, x.type) : subsume(x.type, t);
  const i = indexOf(x);
  if (i < 0) return terr(`undefined tmeta ${showType(x)}`);
  if (x === t) return;
  if (t.tag === 'TMeta') {
    if (t.type) return subsumeTMeta(x, t.type, right);
    const j = indexOf(t);
    if (j < 0) return terr(`undefined tmeta ${showType(t)}`);
    return i > j ? solve(x, i, t) : solve(t, j, x);
  }
  if (t.tag === 'TCon') return solve(x, i, t);
  if (t.tag === 'TVar') {
    const j = indexOf(t);
    if (j < 0) return terr(`undefined tvar ${showType(t)}`);
    if (j > i)
      return terr(`tvar out of scope ${showType(x)} := ${showType(t)}`);
    return solve(x, i, t);
  }
  if (t.tag === 'TFun') {
    if (hasTMeta(x, t))
      return terr(`occurs check fail ${showType(x)} := ${showType(t)}`);
    const a = TMeta();
    const b = TMeta();
    replace(i, [a, b]);
    const ty = TFun(a, b);
    x.type = ty;
    return right ? subsume(t, ty) : subsume(ty, t);
  }
};
const subsume = (t1, t2) => {
  console.log(`subsume ${showTypeR(t1)} <: ${showTypeR(t2)} | ${showDeps()}`);
  if (t1.tag === 'TCon' && t2.tag === 'TCon' && t1 === t2) return;
  if (t1.tag === 'TVar' && t2.tag === 'TVar' && t1 === t2) {
    if (indexOf(t1) < 0)
      return terr(`undefined tvar ${showType(t1)}`);
    return;
  }
  if (t1.tag === 'TFun' && t2.tag === 'TFun') {
    subsume(t2.left, t1.left);
    return subsume(t1.right, t2.right);
  }
  if (t2.tag === 'TForall') {
    deplist.push(t2.name);
    return subsume(t1, t2.type);
  }
  if (t1.tag === 'TForall') {
    const tm = TMeta();
    deplist.push(tm);
    return subsume(openTForall(tm, t1), t2);
  }
  if (t1.tag === 'TMeta') return subsumeTMeta(t1, t2, false);
  if (t2.tag === 'TMeta') return subsumeTMeta(t2, t1, true);
  return terr(`cannot subsume ${showType(t1)} <: ${showType(t2)}`);
};
const unify = (t1, t2) => {
  subsume(t1, t2);
  subsume(t2, t1);
};

// local env
const Nil = { tag: 'Nil' };
const Cons = (head, tail) => ({ tag: 'Cons', head, tail });
const extend = (k, v, l) => Cons([k, v], l);
const lookup = (k, l) => {
  let c = l;
  while (c.tag === 'Cons') {
    const [k2, v] = c.head;
    if (k === k2) return v;
    c = c.tail;
  }
  return null;
};

// ast
const Var = name => ({ tag: 'Var', name });
const Abs = (name, body) => ({ tag: 'Abs', name, body });
const App = (left, right) => ({ tag: 'App', left, right });
const Ann = (term, type) => ({ tag: 'Ann', term, type });

const abs = (ns, t) => ns.reduceRight((x, y) => Abs(y, x), t);
const appFrom = a => a.reduce(App);
function app() { return appFrom(Array.from(arguments)) }

const showTerm = t => {
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Abs') return `(\\${t.name} -> ${showTerm(t.body)})`;
  if (t.tag === 'App')
    return `(${showTerm(t.left)} ${showTerm(t.right)})`;
  if (t.tag === 'Ann')
    return `(${showTerm(t.term)} : ${showType(t.type)})`;
};

// wf
const wfType = t => {
  if (t.tag === 'TVar') {
    if (indexOf(t) < 0) return terr(`undefined tvar ${showType(t)}`);
    return;
  }
  if (t.tag === 'TMeta') {
    if (t.type) return wfType(t.type);
    if (indexOf(t) < 0) return terr(`undefined tmeta ${showType(t)}`);
    return;
  }
  if (t.tag === 'TFun') {
    wfType(t.left);
    wfType(t.right);
    return;
  }
  if (t.tag === 'TForall') {
    const m = Marker();
    deplist.push(m, t.name);
    wfType(t.type);
    drop(m);
    return;
  }
};

// inference
const generalize = (m, t) => {
  const dropped = drop(m);
  const tms = tmetas(t, dropped.filter(t => t.tag === 'TMeta'));
  const l = tms.length;
  const tvs = Array(l);
  for (let i = 0; i < l; i++) {
    const c = tms[i];
    const tv = TVar(`\$${c.id}`);
    c.type = tv;
    tvs[i] = tv;
  }
  return tforall(tvs, t);
};

const infer = term => {
  const m = Marker();
  deplist.push(m);
  const ty = synth(Nil, term);
  return prune(generalize(m, ty));
};

const synth = (env, term) => {
  console.log(`synth ${showTerm(term)}`);
  if (term.tag === 'Var') {
    const t = lookup(term.name, env);
    if (!t) return terr(`undefined var ${term.name}`);
    return t;
  }
  if (term.tag === 'Ann') {
    wfType(term.type);
    check(env, term.term, term.type);
    return term.type;
  }
  if (term.tag === 'App') {
    const ty = synth(env, term.left);
    return synthapp(env, ty, term.right);
  }
  if (term.tag === 'Abs') {
    const a = TMeta();
    const b = TMeta();
    const m = Marker();
    deplist.push(m, a, b);
    check(extend(term.name, a, env), term.body, b);
    return generalize(m, TFun(a, b));
  }
  return terr(`cannot synth ${showTerm(term)}`);
};
const check = (env, term, type) => {
  console.log(`check ${showTerm(term)} : ${showType(type)}`);
  if (type.tag === 'TForall') {
    const m = Marker();
    deplist.push(m, type.name);
    check(env, term, type.type);
    drop(m);
    return;
  }
  if (term.tag === 'Abs' && type.tag === 'TFun') {
    const m = Marker();
    check(extend(term.name, type.left, env), term.body, type.right);
    drop(m);
    return;
  }
  const ty = synth(env, term);
  subsume(ty, type);
};
const synthapp = (env, type, term) => {
  console.log(`synthapp ${showType(type)} @ ${showTerm(term)}`);
  if (type.tag === 'TForall') {
    const tm = TMeta();
    deplist.push(tm);
    return synthapp(env, openTForall(tm, type), term);
  }
  if (type.tag === 'TFun') {
    check(env, term, type.left);
    return type.right;
  }
  if (type.tag === 'TMeta') {
    if (type.type) return synthapp(env, type.type, term);
    const i = indexOf(type);
    if (i < 0) return terr(`undefined tmeta ${showType(type)}`);
    const a = TMeta();
    const b = TMeta();
    replace(i, [b, a]);
    type.type = TFun(a, b);
    check(env, term, a);
    return b;
  }
  return terr(`cannot synthapp ${showType(type)} @ ${showTerm(term)}`);
};

// testing
const tInt = TCon('Int');
const tt = TVar('t');
const tr = TVar('r');
const v = Var;

const term = app(abs(['x', 'y'], v('x')), abs(['x'], v('x')));
console.log(showTerm(term));
const ty = infer(term);
console.log(showType(ty));
