import { Context } from "./context";
import { GNameStore, GName } from "./names";
import { Type, isTVar, isTMeta, isTFun, isTForall, TFun, TForall } from "./types";
import { impossible } from "./util";

export let context = new Context<GName>();
export const namestore = new GNameStore();

export class InferError extends Error {
  constructor(msg: string) { super(msg) }
}
export const infererr = (msg: string) => { throw new InferError(msg) };

const ctxstack: Context<GName>[] = [];
export const store = () => { ctxstack.push(context.clone()) };
export const restore = () => { context = ctxstack.pop() || context };
export const discard = () => { ctxstack.pop() };

export const apply = (type: Type<GName>, ctx: Context<GName> = context): Type<GName> => {
  if (isTVar(type)) return type;
  if (isTMeta(type)) {
    const t = ctx.lookup('CTMeta', type.name);
    return t && t.type ? apply(t.type, ctx) : type;
  }
  if (isTFun(type)) {
    const left = apply(type.left, ctx);
    const right = apply(type.right, ctx);
    return type.left === left && type.right === right ? type : TFun(left, right);
  }
  if (isTForall(type)) {
    const body = apply(type.type, ctx);
    return type.type === body ? type : TForall(type.name, body);
  }
  return impossible('apply');
};
