import { GName } from "./names";
import { Elem, showElem, ElemFromTag, CMarker, isCTMeta } from "./elems";
import { namestore } from "./inferctx";

type El = Elem<GName>;
type ElType = El['tag'];

export class Context {

  constructor(
    private readonly ctx: El[] = [],
  ) {}

  toString(): string {
    return `[${this.ctx.map(showElem).join(', ')}]`;
  }

  clone(): Context {
    const ctx = this.ctx.slice();
    return new Context(ctx);
  }

  addAll(es: El[]): Context {
    for (let i = 0, l = es.length; i < l; i++)
      this.ctx.push(es[i]);
    return this;
  }
  add(...es: El[]): Context {
    return this.addAll(es);
  }
  append(c: Context): Context {
    return this.addAll(c.ctx);
  }

  indexOf(ty: ElType, name: GName): number {
    const a = this.ctx;
    const l = a.length;
    for (let i = 0; i < l; i++) {
      const c = a[i];
      if (c.tag === ty && c.name === name) return i;
    }
    return -1;
  }
  contains(ty: ElType, name: GName): boolean {
    return this.indexOf(ty, name) >= 0;
  }
  lookup<T extends ElType>(ty: T, name: GName): ElemFromTag<GName>[T] | null {
    return this.ctx[this.indexOf(ty, name)] as ElemFromTag<GName>[T] | null;
  }

  pop(): El | null {
    return this.ctx.pop() || null;
  }

  split(ty: ElType, name: GName): El[] {
    const i = this.indexOf(ty, name);
    if (i < 0) return [];
    const ret = this.ctx.splice(i);
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
    const a = this.ctx;
    const l = a.length;
    for (let i = 0; i < l; i++) {
      const c = a[i];
      if (c.tag === 'CTMeta' && !c.type) return false;
    }
    return true;
  }

  enter(el?: El): GName {
    const m = namestore.fresh('m');
    this.add(CMarker(m));
    if (el) this.add(el);
    return m;
  }
  leave(m: GName): void {
    this.split('CMarker', m);
  }
  leaveWithUnsolved(m: GName): GName[] {
    const ret = this.split('CMarker', m);
    const ns = [];
    for (let i = 0, l = ret.length; i < l; i++) {
      const c = ret[i];
      if (isCTMeta(c) && !c.type) ns.push(c.name);
    }
    return ns;
  }

}
