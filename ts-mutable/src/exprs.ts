import { impossible } from "./util";
import { Type, showType } from "./types";

export type Expr<N>
  = Var<N>
  | App<N>
  | Abs<N>
  | Anno<N>;

export interface Var<N> {
  readonly tag: 'Var';
  readonly name: N;
}
export const Var = <N>(name: N): Var<N> => ({ tag: 'Var', name });
export const isVar = <N>(expr: Expr<N>): expr is Var<N> => expr.tag === 'Var';

export interface App<N> {
  readonly tag: 'App';
  readonly left: Expr<N>;
  readonly right: Expr<N>;
}
export const App = <N>(left: Expr<N>, right: Expr<N>): App<N> =>
  ({ tag: 'App', left, right });
export const isApp = <N>(expr: Expr<N>): expr is App<N> => expr.tag === 'App';

export interface Abs<N> {
  readonly tag: 'Abs';
  readonly name: N;
  readonly expr: Expr<N>;
}
export const Abs = <N>(name: N, expr: Expr<N>): Abs<N> =>
  ({ tag: 'Abs', name, expr });
export const isAbs = <N>(expr: Expr<N>): expr is Abs<N> => expr.tag === 'Abs';

export interface Anno<N> {
  readonly tag: 'Anno';
  readonly expr: Expr<N>;
  readonly type: Type<N>;
}
export const Anno = <N>(expr: Expr<N>, type: Type<N>): Anno<N> =>
  ({ tag: 'Anno', expr, type });
export const isAnno = <N>(expr: Expr<N>): expr is Anno<N> => expr.tag === 'Anno';

export const showExpr = <N>(expr: Expr<N>): string => {
  if (isVar(expr)) return `${expr.name}`;
  if (isApp(expr)) return `(${showExpr(expr.left)} ${showExpr(expr.right)})`;
  if (isAbs(expr)) return `(\\${expr.name}. ${showExpr(expr.expr)})`;
  if (isAnno(expr)) return `(${showExpr(expr.expr)} ${showType(expr.type)})`;
  return impossible('showExpr');
};

export const substVar = <N>(expr: Expr<N>, v: N, s: Expr<N>): Expr<N> => {
  if (isVar(expr)) return expr.name === v ? s : expr;
  if (isApp(expr)) {
    const left = substVar(expr.left, v, s);
    const right = substVar(expr.right, v, s);
    return expr.left === left && expr.right === right ? expr : App(left, right);
  }
  if (isAbs(expr)) {
    if (expr.name === v) return expr;
    const body = substVar(expr.expr, v, s);
    return expr.expr === body ? expr : Abs(expr.name, body);
  }
  if (isAnno(expr)) {
    const body = substVar(expr.expr, v, s);
    return expr.expr === body ? expr : Anno(body, expr.type);
  }
  return impossible('substVar');
};
export const openAbs = <N>(a: Abs<N>, s: Expr<N>): Expr<N> =>
  substVar(a.expr, a.name, s);
