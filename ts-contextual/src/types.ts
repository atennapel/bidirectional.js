import { Name, showName, eqName } from './names';
import { impossible } from './util';

export type Type = TVar | TEx | TFun | TForall;

const TVAR = 'TVar';
export interface TVar {
  tag: typeof TVAR,
  name: Name;
}
export const isTVar = (type: Type): type is TVar => type.tag === TVAR;
export const tvar = (name: Name): TVar => ({ tag: TVAR, name });

const TEX = 'TEx';
export interface TEx {
  tag: typeof TEX,
  name: Name;
}
export const isTEx = (type: Type): type is TEx => type.tag === TEX;
export const tex = (name: Name): TEx => ({ tag: TEX, name });

const TFUN = 'TFun';
export interface TFun {
  tag: typeof TFUN,
  left: Type;
  right: Type;
}
export const isTFun = (type: Type): type is TFun => type.tag === TFUN;
export const tfun = (left: Type, right: Type): TFun => ({ tag: TFUN, left, right });
export const tfuns = (ts: Type[]): Type => ts.reduceRight((a, b) => tfun(b, a));

const TFORALL = 'TForall';
export interface TForall {
  tag: typeof TFORALL,
  name: Name;
  type: Type;
}
export const isTForall = (type: Type): type is TForall => type.tag === TFORALL;
export const tforall = (name: Name, type: Type): TForall => ({ tag: TFORALL, name, type });
export const tforalls = (ns: Name[], type: Type): Type =>
  ns.reduceRight((t, n) => tforall(n, t), type);

export const flattenTFun = (t: TFun): Type[] => {
  const r: Type[] = [];
  let c: Type = t;
  while(isTFun(c)) { r.push(c.left); c = c.right }
  r.push(c);
  return r;
};
export const flattenTForall = (t: TForall): { names: Name[], type: Type } => {
  const names: Name[] = [];
  let type: Type = t;
  while(isTForall(type)) { names.push(type.name); type = type.type }
  return { names, type };
};

const showWrap = (t: Type): string =>
  isTFun(t) || isTForall(t)? `(${showType(t)})`: showType(t);
export const showType = (t: Type): string => {
  if(isTVar(t)) return showName(t.name);
  if(isTEx(t)) return `^${showName(t.name)}`;
  if(isTFun(t)) return flattenTFun(t).map(showWrap).join(' -> ');
  if(isTForall(t)) {
    const f = flattenTForall(t);
    return `forall ${f.names.map(showName).join(' ')}. ${showType(f.type)}`;
  }
  return impossible('showType');
};

export const freeTEx = (t: Type): Name[] => {
  if(isTVar(t)) return [];
  if(isTEx(t)) return [t.name];
  if(isTFun(t)) return freeTEx(t.left).concat(freeTEx(t.right));
  if(isTForall(t)) return freeTEx(t.type);
  return impossible('freeTEx');
};
export const containsTEx = (t: Type, n: Name): boolean => {
  if(isTVar(t)) return false;
  if(isTEx(t)) return eqName(n, t.name);
  if(isTFun(t)) return containsTEx(t.left, n) || containsTEx(t.right, n);
  if(isTForall(t)) return containsTEx(t.type, n);
  return impossible('containsTEx');
};

export const substTEx = (x: Name, s: Type, t: Type): Type => {
  if(isTVar(t)) return t;
  if(isTEx(t)) return eqName(x, t.name)? s: t;
  if(isTFun(t)) return tfun(substTEx(x, s, t.left), substTEx(x, s, t.right));
  if(isTForall(t)) return tforall(t.name, substTEx(x, s, t.type));
  return impossible('substTEx');
};
export const substTVar = (x: Name, s: Type, t: Type): Type => {
  if(isTVar(t)) return eqName(x, t.name)? s: t;
  if(isTEx(t)) return t;
  if(isTFun(t)) return tfun(substTVar(x, s, t.left), substTVar(x, s, t.right));
  if(isTForall(t)) return eqName(x, t.name)? t: tforall(t.name, substTVar(x, s, t.type));
  return impossible('substTVar');
};
export const openForall = (t: TForall, s: Type): Type =>
  substTVar(t.name, s, t.type);

export const isMono = (t: Type): boolean => {
  if(isTVar(t)) return true;
  if(isTEx(t)) return true;
  if(isTFun(t)) return isMono(t.left) && isMono(t.right);
  if(isTForall(t)) return false;
  return impossible('isMono');
};

export type CaseType<T> = {
  [TVAR]?: (val: TVar) => T;
  [TEX]?: (val: TEx) => T;
  [TFUN]?: (val: TFun) => T;
  [TFORALL]?: (val: TForall) => T;
  _?: (val: Type) => T;
};
export const caseType = <R>(o: CaseType<R>) => (val: Type): R => {
  if(o[val.tag]) return (o[val.tag] as any)(val) as R;
  if(o._) return o._(val);
  throw new Error(`caseType failed on ${val.tag}`);
};
export const caseTypeOf = <R>(t: Type, o: CaseType<R>): R =>
  caseType(o)(t);
