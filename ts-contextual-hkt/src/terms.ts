import { Name, showName, eqName } from './names';
import { Type, showType } from './types';
import { impossible } from './util';

export type Term = Var | Abs | App | Anno;

const VAR = 'Var';
export interface Var {
  tag: typeof VAR,
  name: Name;
}
export const isVar = (term: Term): term is Var => term.tag === VAR;
export const vr = (name: Name): Var => ({ tag: VAR, name });

const ABS = 'Abs';
export interface Abs {
  tag: typeof ABS,
  name: Name;
  type: Type | null;
  body: Term;
}
export const isAbs = (term: Term): term is Abs => term.tag === ABS;
export const abs = (name: Name, type: Type | null, body: Term): Abs => ({ tag: ABS, name, type, body });
export const abss = (ns: (Name | [Name, Type | null])[], body: Term): Term =>
  ns.reduceRight((t, n) => Array.isArray(n)? abs(n[0], n[1], t): abs(n, null, t), body);

const APP = 'App';
export interface App {
  tag: typeof APP,
  left: Term;
  right: Term;
}
export const isApp = (term: Term): term is App => term.tag === APP;
export const app = (left: Term, right: Term): App => ({ tag: APP, left, right });
export const apps = (ts: Term[]): Term => ts.reduce(app);

const ANNO = 'Anno';
export interface Anno {
  tag: typeof ANNO,
  term: Term;
  type: Type;
}
export const isAnno = (term: Term): term is Anno => term.tag === ANNO;
export const anno = (term: Term, type: Type): Anno => ({ tag: ANNO, term, type });

export const flattenAbs = (t: Abs): { names: [Name, Type | null][], body: Term } => {
  const names: [Name, Type | null][] = [];
  let body: Term = t;
  while(isAbs(body)) { names.push([body.name, body.type]); body = body.body }
  return { names, body };
};
export const flattenApp = (t: App): Term[] => {
  const r: Term[] = [];
  let c: Term = t;
  while(isApp(c)) { r.push(c.right); c = c.left }
  r.push(c);
  return r.reverse();
};

const showWrap = (t: Term): string =>
  isAbs(t) || isApp(t) || isAnno(t)? `(${showTerm(t)})`: showTerm(t);
export const showTerm = (t: Term): string => {
  if(isVar(t)) return showName(t.name);
  if(isAbs(t)) {
    const f = flattenAbs(t);
    return `\\${f.names.map(([n, t]) => t? `(${showName(n)} : ${showType(t)})`: showName(n)).join(' ')} -> ${isAnno(f.body)? `(${showTerm(f.body)})`: showTerm(f.body)}`;
  }
  if(isApp(t)) return flattenApp(t).map(showWrap).join(' ');
  if(isAnno(t)) return `${showTerm(t.term)} : ${showType(t.type)}`;
  return impossible('showTerm');
};

export const substVar = (x: Name, s: Term, t: Term): Term => {
  if(isVar(t)) return eqName(x, t.name)? s: t;
  if(isAbs(t)) return eqName(x, t.name)? t: abs(t.name, t.type, substVar(x, s, t.body));
  if(isApp(t)) return app(substVar(x, s, t.left), substVar(x, s, t.right));
  if(isAnno(t)) return anno(substVar(x, s, t.term), t.type);
  return impossible('substTVar');
};
export const openAbs = (t: Abs, s: Term): Term =>
  substVar(t.name, s, t.body);

export type CaseTerm<T> = {
  [VAR]?: (val: Var) => T;
  [ABS]?: (val: Abs) => T;
  [APP]?: (val: App) => T;
  [ANNO]?: (val: Anno) => T;
  _?: (val: Term) => T;
};
export const caseTerm = <R>(o: CaseTerm<R>) => (val: Term): R => {
  if(o[val.tag]) return (o[val.tag] as any)(val) as R;
  if(o._) return o._(val);
  throw new Error(`caseTerm failed on ${val.tag}`);
};
export const caseTermOf = <R>(t: Term, o: CaseTerm<R>): R =>
  caseTerm(o)(t);
