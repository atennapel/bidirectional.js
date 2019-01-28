import { Context } from "./context";
import { GName } from "./names";
import { Type, isTForall, isTFun, isTMeta, isTVar } from "./types";
import { impossible } from "./util";

export const wfType = (ctx: Context, type: Type<GName>): boolean => {
  if (isTVar(type)) return ctx.indexOf('CTVar', type.name) >= 0;
  if (isTMeta(type)) return ctx.indexOf('CTMeta', type.name) >= 0;
  if (isTFun(type)) return wfType(ctx, type.left) && wfType(ctx, type.right);
  if (isTForall(type)) return wfType(ctx.add(CTVar()), );
  return impossible('showType');
};
