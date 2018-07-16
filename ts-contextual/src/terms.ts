import { Name, showName, eqName } from './names';
import { Type, showType } from './types';
import { impossible } from './util';

export type Term = Var | Abs | App | Anno;

const VAR = 'VAR';
export interface Var {
  tag: typeof VAR,
  name: Name;
}
export const isVar = (term: Term): term is Var => term.tag === VAR;
export const vr = (name: Name): Var => ({ tag: VAR, name });

const ABS = 'ABS';
export interface Abs {
  tag: typeof ABS,
  name: Name;
  body: Term;
}
export const isAbs = (term: Term): term is Abs => term.tag === ABS;
export const abs = (name: Name, body: Term): Abs => ({ tag: ABS, name, body });
export const abss = (ns: Name[], body: Term): Term =>
  ns.reduceRight((t, n) => abs(n, t), body);

const APP = 'APP';
export interface App {
  tag: typeof APP,
  left: Term;
  right: Term;
}
export const isApp = (term: Term): term is App => term.tag === APP;
export const app = (left: Term, right: Term): App => ({ tag: APP, left, right });
export const apps = (ts: Term[]): Term => ts.reduce(app);

const ANNO = 'ANNO';
export interface Anno {
  tag: typeof ANNO,
  term: Term;
  type: Type;
}
export const isAnno = (term: Term): term is Anno => term.tag === ANNO;
export const anno = (term: Term, type: Type): Anno => ({ tag: ANNO, term, type });

export const flattenAbs = (t: Abs): { names: Name[], body: Term } => {
  const names: Name[] = [];
  let body: Term = t;
  while(isAbs(body)) { names.push(body.name); body = body.body }
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
    return `\\${f.names.map(showName).join(' ')} -> ${isAnno(f.body)? `(${showTerm(f.body)})`: showTerm(f.body)}`;
  }
  if(isApp(t)) return flattenApp(t).map(showWrap).join(' ');
  if(isAnno(t)) return `${showTerm(t.term)} : ${showType(t.type)}`;
  return impossible('showTerm');
};

export const substVar = (x: Name, s: Term, t: Term): Term => {
  if(isVar(t)) return eqName(x, t.name)? s: t;
  if(isAbs(t)) return eqName(x, t.name)? t: abs(t.name, substVar(x, s, t.body));
  if(isApp(t)) return app(substVar(x, s, t.left), substVar(x, s, t.right));
  if(isAnno(t)) return anno(substVar(x, s, t.term), t.type);
  return impossible('substTVar');
};
export const openAbs = (t: Abs, s: Term): Term =>
  substVar(t.name, s, t.body);
