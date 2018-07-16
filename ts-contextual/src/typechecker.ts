import {
  Name, showName, eqName,
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
  substTVar,
  showType,
  openForall,
  isMono,
  tfun,
} from './types'
import {
  Term,
  isVar,
  isAbs,
  isAnno,
  isApp,
  showTerm,
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
  not,
  freshTVar,
  add,
  ctvar,
  showContext,
  freshEx,
  drop,
  isCMarker,
  isCTVar,
  cmarker,
  cex,
  withName,
  isCEx,
  put,
  isOrdered,
  orElse,
  replace,
  findVar,
  runContextual,
  freshVar,
} from './context'
import { impossible } from './util';

const typeWF = (type: Type): Contextual<true> => {
  if(isTVar(type)) return not(findTVar(type.name), `duplicate tvar ${showName(type.name)}`);
  if(isTEx(type)) return not(findEx(type.name), `duplicate tex ^${showName(type.name)}`)
  if(isTFun(type)) return then(typeWF(type.left), typeWF(type.right));
  if(isTForall(type)) return (
    bind(freshTVar(type.name), x =>
    then(add([ctvar(x)]),
    typeWF(openForall(type, tvar(x)))))
  );
  return impossible('typeWF');
};

const subtype = (a: Type, b: Type): Contextual<true> =>
  then(typeWF(a), bind(typeWF(b), () => {
    if(((isTVar(a) && isTVar(b)) ||
        (isTEx(a) && isTEx(b))) &&
        eqName(a.name, b.name))
      return ok;
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
  }));

const solve = (a: Name, b: Type): Contextual<true> =>
  !isMono(b)? err<true>(`polymorphic type in solve ${showName(a)} := ${showType(b)}`):
    bind(drop(withName(isCEx, a)), right =>
    then(typeWF(b),
    add([cex(a, b) as Entry].concat(right))));

const instL = (a: Name, b: Type): Contextual<true> => {
  if(isTEx(b)) return bind(isOrdered(a, b.name), o => o? solve(b.name, tex(a)): solve(a, b));
  return orElse(solve(a, b), () => {
    if(isTFun(b)) return (
      bind(freshEx(a), a1 =>
      bind(freshEx(a), a2 =>
      then(replace(withName(isCEx, a), [
        cex(a2), cex(a1), cex(a, tfun(tex(a1), tex(a2)))
      ]),
      then(instR(b.left, a1),
      bind(apply(b.right), t =>
      instL(a2, t))))))
    );
    if(isTForall(b)) return (
      bind(freshTVar(b.name), x =>
      then(add([ctvar(x)]),
      then(instL(a, openForall(b, tvar(x))),
      then(drop(withName(isCTVar, x)),
      ok))))
    );
    return bind(get, ctx =>
      err<true>(`instL failed: ${showName(a)} := ${showType(b)} in ${showContext(ctx)}`));
  });
};
const instR = (a: Type, b: Name): Contextual<true> => {
  if(isTEx(a)) return bind(isOrdered(b, a.name), o => o? solve(a.name, tex(b)): solve(b, a));
  return orElse(solve(b, a), () => {
    if(isTFun(a)) return (
      bind(freshEx(b), b1 =>
      bind(freshEx(b), b2 =>
      then(replace(withName(isCEx, b), [
        cex(b2), cex(b1), cex(b, tfun(tex(b1), tex(b2)))
      ]),
      then(instL(b1, a.left),
      bind(apply(a.right), t =>
      instR(t, b2))))))
    );
    if(isTForall(a)) return (
      bind(freshEx(a.name), x =>
      then(add([cmarker(x), cex(x)]),
      then(instR(openForall(a, tex(x)), b),
      then(drop(withName(isCMarker, x)),
      ok))))
    );
    return bind(get, ctx =>
      err<true>(`instR failed: ${showType(a)} =: ${showName(b)} in ${showContext(ctx)}`));
  });
};

const synthT = (e: Term): Contextual<Type> => {
  if(isVar(e)) return findVar(e.name);
  if(isAbs(e))
  if(isApp(e)) return (
    bind(synthT(e.left), ft =>
    bind(apply(ft), ft =>
    synthappT(ft, e.right)))
  );
  if(isAnno(e)) return (
    then(typeWF(e.type),
    then(checkT(e.term, e.type),
    pure(e.type)))
  );
  return err(`cannot infer ${showTerm(e)}`);
};
const checkT = (e: Term, t: Type): Contextual<true> => {
  if(isTForall(t)) return (
    bind(freshTVar(t.name), x =>
    then(add([ctvar(x)]),
    then(checkT(e, openForall(t, tvar(x))),
    then(drop(withName(isCTVar, x)),
    ok))))
  );
  if(isAbs(e) && isTFun(t)) return (
    bind(freshVar(e.name), x =>
    then(add([]),
    then())
  );
  return (
    bind(synthT(e), te =>
    bind(applies([te, t]), ([te, t]) =>
    subtype(te, t)))
  );
};
const synthappT = (t: Type, e: Term): Contextual<Type> => {
  if(isTForall(t)) return (
    bind(freshEx(t.name), x =>
    then(add([cex(x)]),
    synthappT(openForall(t, tex(x)), e)))
  );
  if(isTEx(t)) return (
    then(findEx(t.name),
    bind(freshEx(t.name), a1 =>
    bind(freshEx(t.name), a2 =>
    then(replace(withName(isCEx, t.name), [
      cex(a2), cex(a1), cex(t.name, tfun(tex(a1), tex(a2)))
    ]),
    then(checkT(e, tex(a1)),
    pure(tex(a2)))))))
  );
  if(isTFun(t)) return then(checkT(e, t.left), pure(t.right));
  return err(`cannot synthapp ${t} with ${e}`);
};

const infer = (ctx: Context, e: Term): Type =>
  runContextual(bind(synthT(e), apply), ctx);
