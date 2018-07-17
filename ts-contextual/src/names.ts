import { impossible } from './util';

export type Name = Str | Gen;

const STR = 'STR';
export interface Str {
  tag: typeof STR;
  name: string;
}
export const str = (name: string): Str => ({ tag: STR, name });
export const isStr = (name: Name): name is Str => name.tag === STR;

const GEN = 'GEN';
export interface Gen {
  tag: typeof GEN;
  name: string;
  index: number;
}
export const gen = (name: string, index: number): Gen => ({ tag: GEN, name, index });
export const isGen = (name: Name): name is Gen => name.tag === GEN;

export const showName = (x: Name): string => {
  if(isStr(x)) return x.name;
  if(isGen(x)) return `${x.name}\$${x.index}`;
  return impossible('strName');
}

export const eqName = (a: Name, b: Name): boolean => {
  if(isStr(a) && isStr(b)) return a.name === b.name;
  if(isGen(a) && isGen(b)) return a.name === b.name && a.index === b.index;
  return false;
}

const incName = (x: Name): Name => {
  if(isStr(x)) return gen(x.name, 0);
  if(isGen(x)) return gen(x.name, x.index + 1);
  return impossible('incName');
}

export const fresh = (ns: Name[], x: Name): Name => {
  let c = x;
  for(let i = 0; i < ns.length; i++) {
    if(eqName(c, ns[i])) {
      c = incName(c);
      i = -1;
    }
  }
  return c;
}

export const freshAll = (ns: Name[], xs: Name[]): Name[] => {
  const r: Name[] = [];
  let c = ns.slice(0);
  for(let i = 0; i < xs.length; i++) {
    const n = fresh(c, xs[i]);
    r.push(n);
    c.push(n);
  }
  return r;
}

export const containsName = (ns: Name[], n: Name): boolean => {
  for(let i = 0; i < ns.length; i++)
    if(eqName(n, ns[i])) return true;
  return false;
};
