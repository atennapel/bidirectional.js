import { GName } from "./names";
import { Type, isTVar, isTMeta, isTFun, isTForall, showType, openTForall, TMeta, TVar, containsTMeta, TFun, isMono } from "./types";
import { infererr, apply, namestore, context, store, InferError, restore, discard } from "./inferctx";
import { CTVar, CTMeta } from "./elems";
import { wfType } from "./wellformedness";

const solve = (x: TMeta<GName>, type: Type<GName>): void => {
  if (!isMono(type))
    return infererr(`cannot solve with polytype: ${showType(x)} := ${showType(type)}`);
  const right = context.split('CTMeta', x.name);
  wfType(type);
  context.add(CTMeta(x.name, type));
  context.addAll(right);
};

const instL = (x: TMeta<GName>, type: Type<GName>): void => {
  store();
  try {
    solve(x, type);
    discard();
  } catch (err) {
    if (!(err instanceof InferError)) throw err;
    restore();
    if (isTMeta(type)) return solve(type, x);
    if (isTFun(type)) {
      const y = x.name;
      const a = namestore.fresh(y);
      const b = namestore.fresh(y);
      const ta = TMeta(a);
      const tb = TMeta(b);
      context.replace('CTMeta', y, [
        CTMeta(b),
        CTMeta(a),
        CTMeta(y, TFun(ta, tb)),
      ]);
      instR(type.left, ta);
      instL(tb, apply(type.right));
      return;
    }
    if (isTForall(type)) {
      const y = namestore.fresh(type.name);
      const m = namestore.fresh('m');
      context.enter(m, CTVar(y));
      instL(x, openTForall(type, TVar(y)));
      context.leave(m);
      return;
    }
    return infererr(`instL failed: ${showType(x)} := ${showType(type)}`);
  }
};

const instR = (type: Type<GName>, x: TMeta<GName>): void => {
  store();
  try {
    solve(x, type);
    discard();
  } catch (err) {
    if (!(err instanceof InferError)) throw err;
    restore();
    if (isTMeta(type)) return solve(type, x);
    if (isTFun(type)) {
      const y = x.name;
      const a = namestore.fresh(y);
      const b = namestore.fresh(y);
      const ta = TMeta(a);
      const tb = TMeta(b);
      context.replace('CTMeta', y, [
        CTMeta(b),
        CTMeta(a),
        CTMeta(y, TFun(ta, tb)),
      ]);
      instL(ta, type.left);
      instR(apply(type.right), tb);
      return;
    }
    if (isTForall(type)) {
      const y = namestore.fresh(type.name);
      const m = namestore.fresh('m');
      context.enter(m, CTMeta(y));
      instR(openTForall(type, TMeta(y)), x);
      context.leave(m);
      return;
    }
    return infererr(`instR failed: ${showType(x)} := ${showType(type)}`);
  }
};

export const subsume = (a: Type<GName>, b: Type<GName>): void => {
  if (a === b) return;
  if (isTVar(a) && isTVar(b) && a.name === b.name) return;
  if (isTMeta(a) && isTMeta(b) && a.name === b.name) return;
  if (isTFun(a) && isTFun(b)) {
    subsume(b.left, a.left);
    subsume(apply(a.right), apply(b.right));
    return;
  }
  if (isTForall(a)) {
    const x = namestore.fresh(a.name);
    const m = namestore.fresh('m');
    context.enter(m, CTMeta(x));
    subsume(openTForall(a, TMeta(x)), b);
    context.leave(m);
    return;
  }
  if (isTForall(b)) {
    const x = namestore.fresh(b.name);
    const m = namestore.fresh('m');
    context.enter(m, CTVar(x));
    subsume(a, openTForall(b, TVar(x)));
    context.leave(m);
    return;
  }
  if (isTMeta(a)) {
    if (containsTMeta(b, a.name))
      return infererr(`occurs check L failed: ${showType(a)} in ${showType(b)}`);
    instL(a, b);
    return;
  }
  if (isTMeta(b)) {
    if (containsTMeta(a, b.name))
      return infererr(`occurs check R failed: ${showType(b)} in ${showType(a)}`);
    instR(a, b);
    return;
  }
  return infererr(`subsume failed: ${showType(a)} <: ${showType(b)}`);
};
