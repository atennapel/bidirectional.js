import { Elem, showElem, ElemFromTag, CMarker, isCTMeta, ElemTag } from "./elems";

export class Context<N> {

  constructor(
    private readonly ctx: Elem<N>[] = [],
  ) {}

  toString(): string {
    return `[${this.ctx.map(showElem).join(', ')}]`;
  }

  clone(): Context<N> {
    const ctx = this.ctx.slice();
    return new Context(ctx);
  }

  addAll(es: Elem<N>[]): Context<N> {
    for (let i = 0, l = es.length; i < l; i++)
      this.ctx.push(es[i]);
    return this;
  }
  add(...es: Elem<N>[]): Context<N> {
    return this.addAll(es);
  }
  append(c: Context<N>): Context<N> {
    return this.addAll(c.ctx);
  }

  indexOf(ty: ElemTag, name: N): number {
    const a = this.ctx;
    const l = a.length;
    for (let i = 0; i < l; i++) {
      const c = a[i];
      if (c.tag === ty && c.name === name) return i;
    }
    return -1;
  }
  contains(ty: ElemTag, name: N): boolean {
    return this.indexOf(ty, name) >= 0;
  }
  lookup<T extends ElemTag>(ty: T, name: N): ElemFromTag<N>[T] | null {
    return (this.ctx[this.indexOf(ty, name)] || null) as ElemFromTag<N>[T] | null;
  }

  pop(): Elem<N> | null {
    return this.ctx.pop() || null;
  }

  split(ty: ElemTag, name: N): Elem<N>[] {
    const i = this.indexOf(ty, name);
    if (i < 0) return [];
    const ret = this.ctx.splice(i);
    ret.shift();
    return ret;
  }

  replace(ty: ElemTag, name: N, es: Elem<N>[]): Context<N> {
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

  enter(m: N, ...es: Elem<N>[]): void {
    this.add(CMarker(m));
    this.addAll(es);
  }
  leave(m: N): void {
    this.split('CMarker', m);
  }
  leaveWithUnsolved(m: N): N[] {
    const ret = this.split('CMarker', m);
    const ns = [];
    for (let i = 0, l = ret.length; i < l; i++) {
      const c = ret[i];
      if (isCTMeta(c) && !c.type) ns.push(c.name);
    }
    return ns;
  }

}
