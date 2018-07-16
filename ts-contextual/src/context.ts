import { Name, showName, eqName, fresh } from './names';
import { Type, showType, isTVar, isTEx, isTFun, isTForall, tforall, tfun } from './types';
import { impossible } from './util';
import { isRegExp } from 'util';

export type Entry = CVar | CTVar | CEx | CMarker;

const CVAR = 'CVAR';
export interface CVar {
  tag: typeof CVAR,
  name: Name;
  type: Type;
}
export const isCVar = (entry: Entry): entry is CVar => entry.tag === CVAR;
export const cvar = (name: Name, type: Type): CVar => ({ tag: CVAR, name, type });

const CTVAR = 'CTVAR';
export interface CTVar {
  tag: typeof CTVAR,
  name: Name;
}
export const isCTVar = (entry: Entry): entry is CTVar => entry.tag === CTVAR;
export const ctvar = (name: Name): CTVar => ({ tag: CTVAR, name });

const CEX = 'CEX';
export interface CEx {
  tag: typeof CEX,
  name: Name;
  type: Type | null;
}
export const isCEx = (entry: Entry): entry is CEx => entry.tag === CEX;
export const cex = (name: Name, type?: Type): CEx => ({ tag: CEX, name, type: type || null });

const CMARKER = 'CMARKER';
export interface CMarker {
  tag: typeof CMARKER,
  name: Name;
}
export const isCMarker = (entry: Entry): entry is CMarker => entry.tag === CMARKER;
export const cmarker = (name: Name): CMarker => ({ tag: CMARKER, name });

export const showEntry = (t: Entry): string => {
  if(isCVar(t)) return `${showName(t.name)} : ${showType(t.type)}`;
  if(isCTVar(t)) return `${showName(t.name)}`;
  if(isCEx(t)) return `^${showName(t.name)}${t.type? ` = ${showType(t.type)}`: ''}`;
  if(isCMarker(t)) return `|>${showName(t.name)}`;
  return impossible('showEntry');
};

export const withName = (fn: (entry: Entry) => boolean, name: Name) =>
  (entry: Entry) => fn(entry) && eqName(name, entry.name);

export type Context = Entry[];

export const showContext = (c: Context): string => `[${c.map(showEntry).join(', ')}]`;

export const contextApply = (c: Context, t: Type): Type => {
  if(isTVar(t)) return t;
  if(isTEx(t)) {
    for(let i = c.length - 1; i >= 0; i--) {
      const e = c[i];
      if(isCEx(e) && eqName(t.name, e.name))
        return e.type? contextApply(c, e.type): t;
    }
    return t;
  }
  if(isTFun(t)) return tfun(contextApply(c, t.left), contextApply(c, t.right));
  if(isTForall(t)) return tforall(t.name, contextApply(c, t.type));
  return impossible('contextApply');
};

// contextual monad
export type Contextual<T> = (ctx: Context) => { ctx: Context, val: T | TypeError };

export const pure = <T>(val: T): Contextual<T> => ctx =>
  ({ ctx, val })
export const err = <T>(msg: string | TypeError): Contextual<T> => ctx =>
  ({ ctx, val: msg instanceof TypeError? msg: new TypeError(msg) });
export const ok = pure<true>(true);

export const get: Contextual<Context> = ctx =>
  ({ ctx, val: ctx });
export const put = (ctx: Context): Contextual<true> => () =>
  ({ ctx, val: true });
export const modify = (fn: (ctx: Context) => Context): Contextual<true> => ctx =>
  ({ ctx: fn(ctx), val: true });

export const map = <A, B>(c: Contextual<A>, fn: (val: A) => B): Contextual<B> => ctx => {
  const r = c(ctx);
  return { ctx: r.ctx, val: r.val instanceof TypeError? r.val: fn(r.val) };
};
export const bind = <A, B>(c: Contextual<A>, fn: (val: A) => Contextual<B>): Contextual<B> => ctx => {
  const r = c(ctx);
  return r.val instanceof TypeError? err<B>(r.val)(r.ctx): fn(r.val)(r.ctx);
};
export const then = <A, B>(c: Contextual<A>, d: Contextual<B>): Contextual<B> =>
  bind(c, () => d);

export const not = <T>(c: Contextual<T>, msg: string): Contextual<true> => ctx => {
  const r = c(ctx);
  return r.val instanceof TypeError? ok(r.ctx): err<true>(msg)(r.ctx);
};
export const check = (c: boolean, msg: string): Contextual<true> =>
  not(pure(c), msg);

export const orElse = <T>(a: Contextual<T>, b: () => Contextual<T>): Contextual<T> => ctx => {
  const r = a(ctx);
  return r.val instanceof TypeError? b()(ctx): r;
};

export const runContextual = <T>(a: Contextual<T>, ctx: Context): T => {
  const r = a(ctx);
  if(r.val instanceof TypeError) throw r.val;
  return r.val;
};

// methods
export const add = (suffix: Context): Contextual<true> =>
  modify(ctx => ctx.concat(suffix));
export const pop: Contextual<Entry> =
  bind(get, ctx =>
  then(put(ctx.slice(0, -1)),
  pure(ctx[ctx.length - 1])));

export const apply = (type: Type): Contextual<Type> =>
  bind(get, ctx => pure(contextApply(ctx, type)));
export const applies = (ts: Type[]): Contextual<Type[]> =>
  bind(get, ctx => pure(ts.map(t => contextApply(ctx, t))));

export const withContext = <T>(c: Context, d: Contextual<T>): Contextual<T> =>
  bind(get, ctx =>
  then(put(c),
  bind(d, v =>
  then(put(ctx),
  pure(v)))));

export const find = <T>(fn: (entry: Entry, i: number) => T | null, msg: (ctx: Context) => string): Contextual<T> =>
  bind(get, ctx => {
    for(let i = ctx.length - 1; i >= 0; i--) {
      const e = fn(ctx[i], i);
      if(e !== null) return pure(e);
    }
    return err(msg(ctx));
  });

export const findVar = (name: Name): Contextual<Type> =>
  find(
    e => isCVar(e) && eqName(name, e.name)? e.type: null,
    ctx => `var ${showName(name)} not found in ${showContext(ctx)}`
  );
export const findTVar = (name: Name): Contextual<true> =>
  find(
    e => isCTVar(e) && eqName(name, e.name)? true: null,
    ctx => `tvar ${showName(name)} not found in ${showContext(ctx)}`
  );
export const findEx = (name: Name): Contextual<Type | null> =>
  find(
    e => isCEx(e) && eqName(name, e.name)? e.type: null,
    ctx => `ex ^${showName(name)} not found in ${showContext(ctx)}`
  );
export const findMarker = (name: Name): Contextual<true> =>
  find(
    e => isCMarker(e) && eqName(name, e.name)? true: null,
    ctx => `marker |>${showName(name)} not found in ${showContext(ctx)}`
  );

export const findIndex = (fn: (e: Entry) => boolean): Contextual<number> =>
  find((e, i) => fn(e)? i: null, ctx => `findIndex failed, element not found`)
export const drop = (fn: (e: Entry) => boolean): Contextual<Context> =>
  bind(findIndex(fn), i =>
  bind(get, ctx => {
    const left = ctx.slice(0, i);
    const right = ctx.slice(i + 1);
    return then(put(left), pure(right));
  }));
export const replace = (fn: (entry: Entry) => boolean, ctx: Context): Contextual<true> =>
  bind(drop(fn), right =>
  then(add(ctx.concat(right)),
  ok));

export const isOrdered = (a: Name, b: Name): Contextual<boolean> =>
  bind(findIndex(withName(isCEx, a)), i =>
  bind(findIndex(withName(isCEx, b)), j =>
  pure(i < j)));

export const vars: Contextual<Name[]> =
  bind(get, ctx =>  
  pure(ctx.filter(e => isCVar(e)).map(e => e.name)));
export const tvars: Contextual<Name[]> =
  bind(get, ctx =>  
  pure(ctx.filter(e => isCTVar(e)).map(e => e.name)));
export const exs: Contextual<Name[]> =
  bind(get, ctx =>
  pure(ctx.filter(e => isCEx(e)).map(e => e.name)));

export const freshIn = (c: Contextual<Name[]>, name: Name): Contextual<Name> =>
  bind(c, ns => pure(fresh(ns, name)));
export const freshVar = (name: Name): Contextual<Name> => freshIn(vars, name);
export const freshTVar = (name: Name): Contextual<Name> => freshIn(tvars, name);
export const freshEx = (name: Name): Contextual<Name> => freshIn(exs, name);
