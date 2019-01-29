import { Abs, Var, showExpr, App } from "./exprs";
import { infer } from "./inference";
import { showType, TForall, TFun, TVar } from "./types";
import { namestore, context } from "./inferctx";
import { CVar } from "./elems";

const x = namestore.fresh('x');
const y = namestore.fresh('y');
const choose = namestore.fresh('choose');

context.add(
  CVar(choose, TForall(x, TFun(TVar(x), TFun(TVar(x), TVar(x))))),
);

const expr = App(Var(choose), Abs(x, Var(x)));
console.log(showExpr(expr));
const microtime = require('microtime');
try {
  let time = microtime.now();
  const type = infer(expr);
  time = microtime.now() - time;
  console.log(showType(type));
  console.log(`${time}us`);
} catch(err) {
  console.log('' + err);
}
