import { Abs, Var, showExpr } from "./exprs";
import { infer } from "./inference";
import { showType } from "./types";
import { namestore } from "./inferctx";

const x = namestore.fresh('x');

const expr = Abs(x, Var(x));
console.log(showExpr(expr));
const microtime = require('microtime');
try {
  let time = microtime.now();
  const type = infer(expr);
  time = microtime.now() - time;
  console.log(showType(type));
  console.log(`${time}`);
} catch(err) {
  console.log('' + err);
}
