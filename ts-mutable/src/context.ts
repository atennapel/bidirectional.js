import { GName } from "./names";
import { Elem, showElem, ElemFromTag, CTMeta, CMarker } from "./elems";
import { cloneMap } from "./util";
import { namestore } from "./inferctx";

type El = Elem<GName>;
type ElType = El['tag'];
type IxMap = { [key in ElType]: Map<GName, number> };

export class Context {

  constructor(
    private readonly ctx: El[] = [],
    private readonly ix: IxMap = {
      CTVar: new Map(),
      CTMeta: new Map(),
      CVar: new Map(),
      CMarker: new Map(),
    },
    private readonly stack: GName[] = [],
  ) {}

  toString(): string {
    return `[${this.ctx.map(showElem).join(', ')}]`;
  }

  clone(): Context {
    const ctx = this.ctx.slice();
    const ix: IxMap = {
      CTVar: cloneMap(this.ix.CTVar),
      CTMeta: cloneMap(this.ix.CTMeta),
      CVar: cloneMap(this.ix.CVar),
      CMarker: cloneMap(this.ix.CMarker),
    };
    const stack = this.stack.slice();
    return new Context(ctx, ix, stack);
  }

  addAll(es: El[]): Context {
    for (let i = 0, l = es.length; i < l; i++) {
      const e = es[i];
      const j = this.ctx.length;
      this.ctx.push(e);
      this.ix[e.tag].set(e.name, j);
    }
    return this;
  }
  add(...es: El[]): Context {
    return this.addAll(es);
  }
  append(c: Context): Context {
    return this.addAll(c.ctx);
  }

  indexOf(ty: ElType, name: GName): number {
    const res = this.ix[ty].get(name);
    return typeof res === 'undefined' ? -1 : res;
  }
  contains(ty: ElType, name: GName): boolean {
    return this.indexOf(ty, name) >= 0;
  }
  lookup<T extends ElType>(ty: T, name: GName): ElemFromTag<GName>[T] | null {
    return this.ctx[this.indexOf(ty, name)] as ElemFromTag<GName>[T] | null;
  }

  pop(): El | null {
    const el = this.ctx.pop() || null;
    const i = this.ctx.length;
    if (el) {
      const j = this.ix[el.tag].get(el.name);
      if (i === j) this.ix[el.tag].delete(el.name);
    }
    return el;
  }

  split(ty: ElType, name: GName): El[] {
    const i = this.indexOf(ty, name);
    if (i < 0) return [];
    const ret = this.ctx.splice(i);
    for (let i = 0, l = ret.length; i < l; i++) {
      const e = ret[i];
      this.ix[e.tag].delete(e.name);
    }
    ret.shift();
    return ret;
  }

  replace(ty: ElType, name: GName, es: El[]): Context {
    const right = this.split(ty, name);
    this.addAll(es);
    this.addAll(right);
    return this;
  }

  isComplete(): boolean {
    const m = this.ix.CTMeta;
    for (let k of m.keys()) {
      const e = this.ctx[m.get(k) as number] as CTMeta<GName>;
      if (!e.type) return false;
    }
    return true;
  }

  enter(el: El): GName {
    const m = namestore.fresh('m');
    this.add(CMarker(m));
    this.add(el);
    this.stack.push(m);
    return m;
  }
  enterWith(els: El[]): GName {
    const m = namestore.fresh('m');
    this.add(CMarker(m));
    this.addAll(els);
    this.stack.push(m);
    return m;
  }
  enterEmpty(): GName {
    const m = namestore.fresh('m');
    this.add(CMarker(m));
    this.stack.push(m);
    return m;
  }
  leave(): El[] {
    const m = this.stack.pop();
    if (!m) return [];
    return this.split('CMarker', m);
  }

}
