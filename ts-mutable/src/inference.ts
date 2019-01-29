import { Expr, isVar, isAbs, isApp, isAnno, showExpr, openAbs, Var } from "./exprs";
import { GName } from "./names";
import { Type, isTForall, isTFun, showType, isTMeta, openTForall, TMeta, TFun, TVar, isTVar, TForall, substTMetas } from "./types";
import { context, infererr, apply, namestore } from "./inferctx";
import { wfType, wfContext } from "./wellformedness";
import { subsume } from "./subsumption";
import { CTMeta, CTVar, CVar, Elem } from "./elems";
import { impossible } from "./util";

// mutates ns and m
const unsolvedInType = (unsolved: GName[], type: Type<GName>, ns: GName[]): void => {
  if (isTVar(type)) return;
  if (isTMeta(type)) {
    const x = type.name;
    if (unsolved.indexOf(x) >= 0 && ns.indexOf(x) < 0) ns.push(x);
    return;
  }
  if (isTFun(type)) {
    unsolvedInType(unsolved, type.left, ns);
    unsolvedInType(unsolved, type.right, ns);
    return;
  }
  if (isTForall(type)) return unsolvedInType(unsolved, type.type, ns);
  return impossible('unsolvedInType');
};

const generalize = (unsolved: GName[], type: Type<GName>): Type<GName> => {
  const ns: GName[] = [];
  unsolvedInType(unsolved, type, ns);
  const m: Map<GName, TVar<GName>> = new Map();
  for (let i = 0, l = ns.length; i < l; i++) {
    const x = ns[i];
    const y = namestore.fresh(x);
    m.set(x, TVar(y));
  }
  let c = substTMetas(type, m);
  for (let i = ns.length - 1; i >= 0; i--)
    c = TForall((m.get(ns[i]) as TVar<GName>).name, c);
  return c;
};

const typesynth = (expr: Expr<GName>): Type<GName> => {
  if (isVar(expr)) {
    const x = context.lookup('CVar', expr.name);
    if (!x) return infererr(`undefined var ${expr.name}`);
    return x.type;
  }
  if (isAbs(expr)) {
    const x = namestore.fresh(expr.name);
    const a = namestore.fresh(expr.name);
    const b = namestore.fresh(expr.name);
    const ta = TMeta(a);
    const tb = TMeta(b);
    context.enterEmpty();
    context.add(CTMeta(a), CTMeta(b), CVar(x, ta));
    typecheck(openAbs(expr, Var(x)), tb);
    const ty = apply(TFun(ta, tb));
    const rest = context.leaveWithUnsolved();
    return generalize(rest, ty);
  }
  if (isApp(expr)) {
    const left = typesynth(expr.left);
    return typeappsynth(apply(left), expr.right);
  }
  if (isAnno(expr)) {
    const ty = expr.type;
    wfType(ty);
    typecheck(expr.expr, ty);
    return ty;
  }
  return infererr(`cannot synth: ${showExpr(expr)}`);
};

const typecheck = (expr: Expr<GName>, type: Type<GName>): void => {
  if (isTForall(type)) {
    const x = namestore.fresh(type.name);
    context.enter(CTVar(x));
    typecheck(expr, openTForall(type, TVar(x)));
    context.leave();
    return;
  }
  if (isAbs(expr) && isTFun(type)) {
    const x = namestore.fresh(expr.name);
    context.enter(CVar(x, type.left));
    typecheck(openAbs(expr, Var(x)), type.right);
    context.leave();
    return;
  }
  const ty = typesynth(expr);
  subsume(apply(ty), apply(type));
};

const typeappsynth = (type: Type<GName>, expr: Expr<GName>): Type<GName> => {
  if (isTForall(type)) {
    const x = namestore.fresh(type.name);
    context.add(CTMeta(x));
    return typeappsynth(openTForall(type, TMeta(x)), expr);
  }
  if (isTMeta(type)) {
    const x = type.name;
    const a = namestore.fresh(x);
    const b = namestore.fresh(x);
    const ta = TMeta(a);
    const tb = TMeta(b);
    context.replace('CTMeta', x, [
      CTMeta(b),
      CTMeta(a),
      CTMeta(x, TFun(ta, tb)),
    ])
    typecheck(expr, ta);
    return tb;
  }
  if (isTFun(type)) {
    typecheck(expr, type.left);
    return type.right;
  }
  return infererr(`cannot typeappsynth: ${showType(type)} @ ${showExpr(expr)}`);
};

export const infer = (expr: Expr<GName>): Type<GName> => {
  namestore.reset();
  wfContext();
  context.enterEmpty();
  const ty = apply(typesynth(expr));
  const rest = context.leaveWithUnsolved();
  const tygen = generalize(rest, ty);
  if (!context.isComplete()) return infererr(`incomplete`);
  return tygen;
};
