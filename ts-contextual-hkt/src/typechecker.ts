import {
  Name,
  showName,
  eqName,
  str,
  containsName,
  freshAll,
  fresh,
} from './names';
import {
  Type,
  isTVar,
  isTEx,
  isTFun,
  isTForall,
  tvar,
  tex,
  containsTEx,
  substTEx,
  showType,
  openForall,
  isMono,
  tfun,
  tforalls,
  freeTEx,

  caseType,
  caseTypeOf,
  isTApp,
  allTVar,
  substTVar,
} from './types'
import {
  Term,
  isAbs,
  showTerm,
  openAbs,
  vr,
  caseTermOf,
} from './terms';
import {
  Entry,
  Context,
  Contextual,
  bind,
  then,
  err,
  pure,
  check,
  ok,
  get,
  apply,
  applies,
  findTVar,
  findEx,
  freshTVar,
  add,
  ctvar,
  showContext,
  freshEx,
  freshExs,
  drop,
  isCMarker,
  isCTVar,
  cmarker,
  cex,
  withName,
  isCEx,
  isOrdered,
  orElse,
  replace,
  findVar,
  runContextual,
  freshVar,
  cvar,
  isCVar,
  contextUnsolved,
  checkComplete,
  log,
  tvars,
} from './context'

const typeWF: (type: Type) => Contextual<true> = 
  caseType({
    TVar: type => findTVar(type.name),
    TEx: type => then(findEx(type.name), ok),
    TApp: type => then(typeWF(type.left), typeWF(type.right)),
    TFun: type => then(typeWF(type.left), typeWF(type.right)),
    TForall: type =>
      bind(freshTVar(type.name), x =>
      then(add([ctvar(x)]),
      typeWF(openForall(type, tvar(x)))))
  });

const solveUnify = (x: Name, t: Type): Contextual<true> =>
  then(log(ctx => `solveUnify ${showName(x)} := ${showType(t)} in ${showContext(ctx)}`),
  bind(drop(withName(isCEx, x)), right =>
  then(typeWF(t),
  add([cex(x, t) as Entry].concat(right)))));

const unify = (a: Type, b: Type): Contextual<true> =>
  then(log(ctx => `unify ${showType(a)} ~ ${showType(b)} in ${showContext(ctx)}`),
  then(typeWF(a), bind(typeWF(b), () => {
    if(((isTVar(a) && isTVar(b)) ||
        (isTEx(a) && isTEx(b))) &&
        eqName(a.name, b.name))
      return ok;
    if(isTEx(a) && isTEx(b))
      return bind(isOrdered(a.name, b.name), c => c? solveUnify(b.name, a): solveUnify(a.name, b));
    if(isTEx(a)) return (
      then(check(!containsTEx(b, a.name), `occurs check failed unify L: ${showType(a)} in ${showType(b)}`),
      solveUnify(a.name, b))
    );
    if(isTEx(b)) return (
      then(check(!containsTEx(a, b.name), `occurs check failed unify R: ${showType(b)} in ${showType(a)}`),
      solveUnify(b.name, a))
    );
    if(isTApp(a) && isTApp(b)) return (
      then(unify(a.left, b.left),
      bind(applies([a.right, b.right]), ([ta, tb]) =>
      unify(ta, tb)))
    );
    if(isTFun(a) && isTFun(b)) return (
      then(unify(a.left, b.left),
      bind(applies([a.right, b.right]), ([ta, tb]) =>
      unify(ta, tb)))
    );
    if(isTForall(a) && isTForall(b)) return bind(tvars, tvs => {
      const v = fresh(tvs.concat(allTVar(a).concat(allTVar(b))), str('s'));
      return unify(openForall(a, tvar(v)), openForall(b, tvar(v)));
    });
    if(isTForall(a)) return (
      bind(freshTVar(a.name), x =>
      then(add([ctvar(x)]), 
      then(subtype(openForall(a, tvar(x)), b),
      then(drop(withName(isCTVar, x)),
      ok))))
    );
    if(isTForall(b)) return (
      bind(freshTVar(b.name), x =>
      then(add([ctvar(x)]), 
      then(subtype(a, openForall(b, tvar(x))),
      then(drop(withName(isCTVar, x)),
      ok))))
    );
    return bind(get, ctx =>
      err<true>(`unify failed ${showType(a)} ~ ${showType(b)} in ${showContext(ctx)}`));
  })));

const subtype = (a: Type, b: Type): Contextual<true> =>
  then(log(ctx => `subtype ${showType(a)} <: ${showType(b)} in ${showContext(ctx)}`),
  then(typeWF(a), bind(typeWF(b), () => {
    if(((isTVar(a) && isTVar(b)) ||
        (isTEx(a) && isTEx(b))) &&
        eqName(a.name, b.name))
      return ok;
    if(isTApp(a) || isTApp(b)) return unify(a, b);
    if(isTFun(a) && isTFun(b)) return (
      then(subtype(b.left, a.left),
      bind(applies([a.right, b.right]), ([ta, tb]) =>
      subtype(ta, tb)))
    );
    if(isTForall(a)) return (
      bind(freshEx(a.name), x =>
      then(add([cmarker(x), cex(x)]), 
      then(subtype(openForall(a, tex(x)), b),
      then(drop(withName(isCMarker, x)),
      ok))))
    );
    if(isTForall(b)) return (
      bind(freshTVar(b.name), x =>
      then(add([ctvar(x)]), 
      then(subtype(a, openForall(b, tvar(x))),
      then(drop(withName(isCTVar, x)),
      ok))))
    );
    if(isTEx(a)) return (
      then(check(!containsTEx(b, a.name), `occurs check failed L: ${showType(a)} in ${showType(b)}`),
      instL(a.name, b))
    );
    if(isTEx(b)) return (
      then(check(!containsTEx(a, b.name), `occurs check failed R: ${showType(b)} in ${showType(a)}`),
      instR(a, b.name))
    );
    return bind(get, ctx =>
      err<true>(`subtype failed ${showType(a)} <: ${showType(b)} in ${showContext(ctx)}`));
  })));

const solve = (a: Name, b: Type): Contextual<true> =>
  then(log(ctx => `solve ${showName(a)} := ${showType(b)} in ${showContext(ctx)}`),
  !isMono(b)? err<true>(`polymorphic type in solve ${showName(a)} := ${showType(b)}`):
    bind(drop(withName(isCEx, a)), right =>
    then(typeWF(b),
    add([cex(a, b) as Entry].concat(right)))));

const instL = (a: Name, b: Type): Contextual<true> =>
  then(log(ctx => `instR ${showName(a)} := ${showType(b)} in ${showContext(ctx)}`),
  isTEx(b)? bind(isOrdered(a, b.name), o => o? solve(b.name, tex(a)): solve(a, b)):
    orElse(solve(a, b), () =>
      caseTypeOf(b, {
        TFun: b =>
          bind(freshExs([a, a]), ([a1, a2]) =>
          then(replace(withName(isCEx, a), [
            cex(a2), cex(a1), cex(a, tfun(tex(a1), tex(a2)))
          ]),
          then(instR(b.left, a1),
          bind(apply(b.right), t =>
          instL(a2, t))))),
        TForall: b =>
          bind(freshTVar(b.name), x =>
          then(add([ctvar(x)]),
          then(instL(a, openForall(b, tvar(x))),
          then(drop(withName(isCTVar, x)),
          ok)))),
        _: b => bind(get, ctx =>
          err<true>(`instL failed: ${showName(a)} := ${showType(b)} in ${showContext(ctx)}`))
      })));

const instR = (a: Type, b: Name): Contextual<true> =>
  then(log(ctx => `instR ${showType(a)} =: ${showName(b)} in ${showContext(ctx)}`),
  isTEx(a)? bind(isOrdered(b, a.name), o => o? solve(a.name, tex(b)): solve(b, a)):
    orElse(solve(b, a), () =>
      caseTypeOf(a, {
        TFun: a =>
          bind(freshExs([b, b]), ([b1, b2]) =>
          then(replace(withName(isCEx, b), [
            cex(b2), cex(b1), cex(b, tfun(tex(b1), tex(b2)))
          ]),
          then(instL(b1, a.left),
          bind(apply(a.right), t =>
          instR(t, b2))))),
        TForall: a =>
          bind(freshEx(a.name), x =>
          then(add([cmarker(x), cex(x)]),
          then(instR(openForall(a, tex(x)), b),
          then(drop(withName(isCMarker, x)),
          ok)))),
        _: a => bind(get, ctx =>
          err<true>(`instR failed: ${showType(a)} =: ${showName(b)} in ${showContext(ctx)}`)),
      })));

const orderedUnsolved = (ctx: Context, t: Type): Name[] => {
  const u = contextUnsolved(ctx);
  const r: Name[] = [];
  const es = freeTEx(t);
  for(let i = 0; i < es.length; i++) {
    const n = es[i];
    if(containsName(u, n) && !containsName(r, n))
      r.push(n);
  }
  return r;
};

const generalize = (x: Name, t: Type): Contextual<Type> =>
  bind(apply(t), t =>
  bind(drop(withName(isCMarker, x)), right =>
  bind(pure(orderedUnsolved(right, t)), u =>
  pure(tforalls(u, u.reduce((t, n) => substTEx(n, tvar(n), t), t))))));

const synthT = (e: Term): Contextual<Type> =>
  then(log(ctx => `synthT ${showTerm(e)} in ${showContext(ctx)}`),
  caseTermOf(e, {
    Var: e =>
      findVar(e.name),
    Abs: e =>
      e.type?
        then(typeWF(e.type),
        bind(freshVar(e.name), x =>
        bind(freshEx(e.name), b =>
        then(add([cmarker(b), cex(b), cvar(x, e.type as Type)]),
        then(checkT(openAbs(e, vr(x)), tex(b)),
        generalize(b, tfun(e.type as Type, tex(b)))))))):

        bind(freshVar(e.name), x =>
        bind(freshExs([e.name, e.name]), ([a, b]) =>
        then(add([cmarker(a), cex(a), cex(b), cvar(x, tex(a))]),
        then(checkT(openAbs(e, vr(x)), tex(b)),
        generalize(a, tfun(tex(a), tex(b))))))),
    App: e =>
      bind(synthT(e.left), ft =>
      bind(apply(ft), ft =>
      synthappT(ft, e.right))),
    Anno: e =>
      then(typeWF(e.type),
      then(checkT(e.term, e.type),
      pure(e.type))),
  }));

const checkT = (e: Term, t: Type): Contextual<true> =>
  then(log(ctx => `checkT ${showTerm(e)} : ${showType(t)} in ${showContext(ctx)}`),
  caseTypeOf(t, {
    TForall: t =>
      bind(freshTVar(t.name), x =>
      then(add([ctvar(x)]),
      then(checkT(e, openForall(t, tvar(x))),
      then(drop(withName(isCTVar, x)),
      ok)))),
    TFun: t => !isAbs(e) || e.type? checksynthT(e, t):
      bind(freshVar(e.name), x =>
      then(add([cvar(x, t.left)]),
      then(checkT(openAbs(e, vr(x)), t.right),
      then(drop(withName(isCVar, x)),
      ok)))),
    _: t => checksynthT(e, t),
  }));
const checksynthT = (e: Term, t: Type): Contextual<true> =>
  then(log(ctx => `checksynthT ${showTerm(e)} : ${showType(t)} in ${showContext(ctx)}`),
  bind(synthT(e), te =>
  bind(applies([te, t]), ([te, t]) =>
  subtype(te, t))));

const synthappT = (t: Type, e: Term): Contextual<Type> =>
  then(log(ctx => `synthappT ${showType(t)} and ${showTerm(e)} in ${showContext(ctx)}`),
  caseTypeOf(t, {
    TForall: t =>
      bind(freshEx(t.name), x =>
      then(add([cex(x)]),
      synthappT(openForall(t, tex(x)), e))),
    TEx: t =>
      then(findEx(t.name),
      bind(freshExs([t.name, t.name]), ([a1, a2]) =>
      then(replace(withName(isCEx, t.name), [
        cex(a2), cex(a1), cex(t.name, tfun(tex(a1), tex(a2)))
      ]),
      then(checkT(e, tex(a1)),
      pure(tex(a2)))))),
    TFun: t =>
      then(checkT(e, t.left), pure(t.right)),
    _: t => err(`cannot synthapp ${t} with ${e}`),
  }));

const synth = (e: Term): Contextual<Type> =>
  bind(freshEx(str('m')), m =>
  then(add([cmarker(m)]),
  bind(synthT(e), t =>
  bind(generalize(m, t), t =>
  then(checkComplete,
  pure(t))))));

export const infer = (ctx: Context, e: Term): { ctx: Context, type: Type } =>
  runContextual(ctx,
    bind(synth(e), type =>
    bind(get, ctx =>
    pure({ ctx, type }))));
