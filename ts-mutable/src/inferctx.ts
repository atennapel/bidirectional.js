import { Context } from "./context";
import { GNameStore } from "./names";

export let context = new Context();
export const namestore = new GNameStore();

export class InferError extends Error {
  constructor(msg: string) { super(msg) }
}
export const infererr = (msg: string) => { throw new InferError(msg) };

const ctxstack: Context[] = [];
export const store = () => { ctxstack.push(context.clone()) };
export const restore = () => { context = ctxstack.pop() || context };
