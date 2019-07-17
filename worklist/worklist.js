// types
let tmetaId = 0;
const freshTMetaId = () => tmetaId++;
const resetTMetaId = () => { tmetaId = 0 };
const TMeta = id => ({ tag: 'TMeta', id, type: null });
const freshTMeta = () => TMeta(freshTMetaId());

const TVar = name => ({ tag: 'TVar', name });
const TApp = (left, right) => ({ tag: 'TApp', left, right });
const TForall = (name, type) => ({ tag: 'TForall', name, type });
const tforall = (ns, t) => ns.reduceRight((t, x) => TForall(x, t), t);

const tFun = TVar('->');
const TFun = (left, right) => TApp(TApp(tFun, left), right);
const isTFun = ty => ty.tag === 'TApp' && ty.left.tag === 'TApp' && ty.left.left === tFun;
const tfunL = ty => ty.left.right;
const tfunR = ty => ty.right;

const showType = type => {
  if (type.tag === 'TMeta') return `?${type.id}${type.type ? `{${showType(type.type)}}` : ''}`;
  if (type.tag === 'TVar') return type.name;
  if (isTFun(type)) return `(${showType(tfunL(type))} -> ${showType(tfunR(type))})`;
  if (type.tag === 'TApp') return `(${showType(type.left)} ${showType(type.right)})`;
  if (type.tag === 'TForall') return `(forall ${type.name}. ${showType(type.type)})`;
};

const pruneTop = type => {
  if (type.tag === 'TMeta') {
    if (!type.type) return type;
    return type.type = pruneTop(type.type);
  }
  return type;
};

const prune = type => {
  if (type.tag === 'TMeta') {
    if (!type.type) return type;
    return type.type = prune(type.type);
  }
  if (type.tag === 'TApp') {
    const l = prune(type.left);
    const r = prune(type.right);
    return l === type.left && r === type.right ? type : TApp(l, r);
  }
  if (type.tag === 'TForall') {
    const b = prune(type.type);
    return b === type.type ? type : TForall(type.name, b);
  }
  return type;
};

const substTVar = (x, s, t) => {
  if (t.tag === 'TVar') return t.name === x ? s : t;
  if (t.tag === 'TApp') {
    const l = substTVar(x, s, t.left);
    const r = substTVar(x, s, t.right);
    return l === t.left && r === t.right ? t : TApp(l, r);
  }
  if (t.tag === 'TForall') {
    if (t.name === x) return t;
    const b = substTVar(x, s, t.type);
    return b === t.type ? t : TForall(t.name, b);
  }
  return t;
};
const openTForall = (tf, t) => substTVar(tf.name, t, tf.type);

const occursTMeta = (m, t) => {
  if (m === t) return true;
  if (t.tag === 'TApp')
    return occursTMeta(m, t.left) || occursTMeta(m, t.right);
  if (t.tag === 'TForall') return occursTMeta(m, t.type);
  return false;
};

const tmetas = (t, a = []) => {
  if (t.tag === 'TMeta') {
    if (t.type) return tmetas(t.type, a);
    if (a.indexOf(t) >= 0) return a;
    a.push(t);
    return a;
  }
  if (t.tag === 'TApp') return tmetas(t.right, tmetas(t.left, a));
  if (t.tag === 'TForall') return tmetas(t.type, a);
  return a;
};

// terms
const Var = name => ({ tag: 'Var', name });
const Abs = (name, body) => ({ tag: 'Abs', name, body });
const AbsT = (name, body, type) => ({ tag: 'AbsT', name, body, type });
const App = (left, right) => ({ tag: 'App', left, right });
const AppT = (left, right) => ({ tag: 'AppT', left, right });
const Ann = (term, type) => ({ tag: 'Ann', term, type });

// todo type applications

const showTerm = term => {
  if (term.tag === 'Var') return term.name;
  if (term.tag === 'Abs') return `(\\${term.name} -> ${showTerm(term.body)})`;
  if (term.tag === 'AbsT')
    return `(/\\${term.name} -> (${showTerm(term.body)} : ${showType(term.type)}))`;
  if (term.tag === 'App') return `(${showTerm(term.left)} ${showTerm(term.right)})`;
  if (term.tag === 'AppT') return `(${showTerm(term.left)} @${showType(term.right)})`;
  if (term.tag === 'Ann') return `(${showTerm(term.term)} : ${showType(term.type)})`;
};

// judgments
const JDone = { tag: 'JDone' };
const JSubtype = (left, right) => ({ tag: 'JSubtype', left, right });
const JCheck = (term, type) => ({ tag: 'JCheck', term, type });
const JSynth = (term, result, cont) => ({ tag: 'JSynth', term, result, cont });
const JSynthapp = (type, term, result, cont) =>
  ({ tag: 'JSynthapp', type, term, result, cont });
const JSynthappT = (type1, type2, result, cont) =>
  ({ tag: 'JSynthappT', type1, type2, result, cont });

const showJudgment = judgment => {
  if (judgment.tag === 'JDone') return 'done';
  if (judgment.tag === 'JSubtype') return `${showType(judgment.left)} <: ${showType(judgment.right)}`;
  if (judgment.tag === 'JCheck') return `${showTerm(judgment.term)} <= ${showType(judgment.type)}`;
  if (judgment.tag === 'JSynth')
    return `${showTerm(judgment.term)} =>${showType(judgment.result)} (${showJudgment(judgment.cont)})`;
  if (judgment.tag === 'JSynthapp')
    return `${showType(judgment.type)} @ ${showTerm(judgment.term)} =>>${showType(judgment.result)} (${showJudgment(judgment.cont)})`;
  if (judgment.tag === 'JSynthappT')
    return `${showType(judgment.type1)} @${showType(judgment.type2)} =>>${showType(judgment.result)} (${showJudgment(judgment.cont)})`;
};

// elems (includes TVar, TMeta and judgments)
const CVar = (name, type) => ({ tag: 'CVar', name, type });

const showElem = elem => {
  if (elem.tag === 'CVar') return `${elem.name} : ${showType(elem.type)}`;
  if (elem.tag === 'TVar' || elem.tag === 'TMeta') return showType(elem);
  return showJudgment(elem);
};

// worklist
const showWorklist = wl => `[${wl.map(showElem).join(', ')}]`;

const findVar = (wl, x) => {
  for (let i = wl.length - 1; i >= 0; i--) {
    const c = wl[i];
    if (c.tag === 'CVar' && c.name === x) return c.type;
  }
  return null;
};
const indexTVar = (wl, x) => {
  for (let i = wl.length - 1; i >= 0; i--) {
    const c = wl[i];
    if (c.tag === 'TVar' && c.name === x) return i;
  }
  return -1;
};
const indexTMeta = (wl, m) => wl.indexOf(m);

const remove = (wl, i) => wl.splice(i, 1);
const replace2 = (wl, i, a, b) => wl.splice(i, 1, a, b);

const initialContext = () => [tFun];

// errors
const terr = msg => { throw new TypeError(msg) };

// wellformedness
const wfTypeR = (wl, t) => {
  if (t.tag === 'TVar') return indexTVar(wl, t.name) >= 0;
  if (t.tag === 'TMeta') return indexTMeta(wl, t) >= 0;
  if (t.tag === 'TApp') return wfTypeR(wl, t.left) && wfTypeR(wl, t.right);
  if (t.tag === 'TForall') {
    wl.push(TVar(t.name));
    return wfTypeR(wl, t.type);
  }
};
const wfType = (wl, t) => {
  const l = wl.length;
  const b = wfTypeR(wl, t);
  wl.splice(l, wl.length);
  return b;
};

// algorithm
const step = wl => {
  const top = wl.pop();
  
  if (top.tag === 'TVar') return;
  if (top.tag === 'TMeta') return;
  if (top.tag === 'CVar') return;

  if (top.tag === 'JDone') return;

  if (top.tag === 'JSubtype') {
    const { left: left_, right: right_ } = top;
    if (left_ === right_) return;
    const left = pruneTop(left_);
    const right = pruneTop(right_);
    if (left === right) return;
    if (left.tag === 'TVar' && right.tag === 'TVar' && left.name === right.name) return;
    if (isTFun(left) && isTFun(right))
      return wl.push(
        JSubtype(tfunR(left), tfunR(right)),
        JSubtype(tfunL(right), tfunL(left))
      );
    if (left.tag === 'TApp' && right.tag === 'TApp')
      return wl.push(
        JSubtype(right.right, left.right),
        JSubtype(left.right, right.right),
        JSubtype(right.left, left.left),
        JSubtype(left.left, right.left),
      );
    if (right.tag === 'TForall')
      return wl.push(TVar(right.name), JSubtype(left, right.type));
    if (left.tag === 'TForall') {
      const m = freshTMeta();
      return wl.push(m, JSubtype(openTForall(left, m), right));
    }
    if (left.tag === 'TMeta' && right.tag === 'TApp') {
      const i = indexTMeta(wl, left);
      if (i < 0) return terr(`undefined tmeta ${showType(left)}`);
      if (occursTMeta(left, right))
        return terr(`occurs check failed ${showJudgment(top)}`);
      const a = freshTMeta();
      const b = freshTMeta();
      const ty = (isTFun(right) ? TFun : TApp)(a, b);
      left.type = ty;
      replace2(wl, i, a, b);
      return wl.push(JSubtype(ty, right));
    }
    if (left.tag === 'TApp' && right.tag === 'TMeta') {
      const i = indexTMeta(wl, right);
      if (i < 0) return terr(`undefined tmeta ${showType(right)}`);
      if (occursTMeta(right, left))
        return terr(`occurs check failed ${showJudgment(top)}`);
      const a = freshTMeta();
      const b = freshTMeta();
      const ty = (isTFun(left) ? TFun : TApp)(a, b);
      right.type = ty;
      replace2(wl, i, a, b);
      return wl.push(JSubtype(left, ty));
    }
    if (left.tag === 'TMeta' && right.tag === 'TMeta') {
      const i = indexTMeta(wl, left);
      if (i < 0) return terr(`undefined tmeta ${showType(left)}`);
      const j = indexTMeta(wl, right);
      if (j < 0) return terr(`undefined tmeta ${showType(right)}`);
      if (i < j) {
        remove(wl, i);
        left.type = right;
      } else {
        remove(wl, j);
        right.type = left;
      }
      return;
    }
    if (left.tag === 'TVar' && right.tag === 'TMeta') {
      const i = indexTVar(wl, left.name);
      if (i < 0) return terr(`undefined tvar ${showType(left)}`);
      const j = indexTMeta(wl, right);
      if (j < 0) return terr(`undefined tmeta ${showType(right)}`);
      if (i > j) return terr(`tvar out of scope ${showJudgment(top)} in ${showWorklist(wl)}`);
      remove(wl, j);
      right.type = left;
      return;
    }
    if (left.tag === 'TMeta' && right.tag === 'TVar') {
      const i = indexTMeta(wl, left);
      if (i < 0) return terr(`undefined tmeta ${showType(left)}`);
      const j = indexTVar(wl, right.name);
      if (j < 0) return terr(`undefined tvar ${showType(right)}`);
      if (j > i) return terr(`tvar out of scope ${showJudgment(top)} in ${showWorklist(wl)}`);
      remove(wl, i);
      left.type = right;
      return;
    }
    terr(`subtype fails ${showJudgment(top)} in ${showWorklist(wl)}`);
  }

  if (top.tag === 'JCheck') {
    const { term, type: type_ } = top;
    const type = pruneTop(type_);
    if (type.tag === 'TForall')
      return wl.push(TVar(type.name), JCheck(term, type.type));
    if (term.tag === 'Abs') {
      if (isTFun(type))
        return wl.push(CVar(term.name, tfunL(type)), JCheck(term.body, tfunR(type)));
      if (type.tag === 'TMeta') {
        const i = indexTMeta(wl, type);
        if (i < 0) return terr(`undefined tmeta ${showType(type)}`);
        const a = freshTMeta();
        const b = freshTMeta();
        const ty = TFun(a, b);
        type.type = ty;
        replace2(wl, i, a, b);
        return wl.push(CVar(term.name, a), JCheck(term.body, b));
      }
    }
    const result = freshTMeta();
    return wl.push(JSynth(term, result, JSubtype(result, type)));
  }

  if (top.tag === 'JSynth') {
    const { term, result, cont } = top;
    if (term.tag === 'Var') {
      const ty = findVar(wl, term.name);
      if (!ty) return terr(`undefined var ${term.name}`);
      result.type = ty;
      return wl.push(cont);
    }
    if (term.tag === 'Ann') {
      if (!wfType(wl, term.type))
        return terr(`type not wellformed: ${showJudgment(top)}`);
      result.type = term.type;
      return wl.push(cont, JCheck(term.term, term.type));
    }
    if (term.tag === 'Abs') {
      const a = freshTMeta();
      const b = freshTMeta();
      result.type = TFun(a, b);
      return wl.push(a, b, cont, CVar(term.name, a), JCheck(term.body, b));
    }
    if (term.tag === 'AbsT') {
      result.type = TForall(term.name, term.type);
      return wl.push(cont, TVar(term.name), JCheck(term.body, term.type));
    }
    if (term.tag === 'App') {
      const result2 = freshTMeta();
      return wl.push(JSynth(term.left, result2, JSynthapp(result2, term.right, result, cont)));
    }
    if (term.tag === 'AppT') {
      const result2 = freshTMeta();
      return wl.push(JSynth(term.left, result2, JSynthappT(result2, term.right, result, cont)));
    }
  }

  if (top.tag === 'JSynthapp') {
    const { type: type_, term, result, cont } = top;
    const type = pruneTop(type_);
    if (type.tag === 'TForall') {
      const a = freshTMeta();
      return wl.push(a, JSynthapp(openTForall(type, a), term, result, cont));
    }
    if (isTFun(type)) {
      result.type = tfunR(type);
      return wl.push(cont, JCheck(term, tfunL(type)));
    }
    if (type.tag === 'TMeta') {
      const i = indexTMeta(wl, type);
      if (i < 0) return terr(`undefined tmeta ${showType(type)}`);
      const a = freshTMeta();
      const b = freshTMeta();
      const ty = TFun(a, b);
      type.type = ty;
      replace2(wl, i, a, b);
      return wl.push(JSynthapp(ty, term, result, cont));
    }
    terr(`cannot synthapp: ${showJudgment(top)}`);
  }

  if (top.tag === 'JSynthappT') {
    const { type1: type1_, type2, result, cont } = top;
    const type1 = pruneTop(type1_);
    if (type1.tag === 'TForall') {
      result.type = openTForall(type1, type2);
      return wl.push(cont);
    }
    terr(`cannot synthappT: ${showJudgment(top)}`);
  }

  terr(`failed to step: ${showJudgment(top)} in ${showWorklist(wl)}`);
};

const steps = wl => {
  while (wl.length > 0) {
    console.log(showWorklist(wl));
    step(wl);
  }
};

const generalize = tm => {
  const tvs = tmetas(tm).map(m => {
    const x = `t${m.id}`;
    m.type = TVar(x);
    return x;
  });
  return tforall(tvs, prune(tm));
};

const infer = (term, ctx = []) => {
  const tm = freshTMeta();
  ctx.push(JSynth(term, tm, JDone));
  steps(ctx);
  return generalize(tm);
};

// testing
const tv = TVar;
const v = Var;
function app() { return Array.from(arguments).reduce(App) }
function tapp() { return Array.from(arguments).reduce(TApp) }
function tfun() { return Array.from(arguments).reduceRight((x, y) => TFun(y, x)) }
const abs = (ns, b) => ns.reduceRight((x, y) => Abs(y, x), b); 
const tList = TVar('List');
const tBool = TVar('Bool');

const tid = TForall('t', TFun(tv('t'), tv('t')));
const id = App(AppT(AbsT('t', Abs('x', Var('x')), TFun(tv('t'), tv('t'))), tid), Abs('y', Var('y')));

const ctx = initialContext();
ctx.push(
  tList,
  tBool,
  CVar('single', tforall(['t'], tfun(tv('t'), tapp(tList, tv('t'))))),
  CVar('True', tBool),
);

const term = abs(['f'], app(v('f'), app(v('single'), v('True'))));
console.log(showTerm(term));
const type = infer(term, ctx);
console.log(showType(type));
