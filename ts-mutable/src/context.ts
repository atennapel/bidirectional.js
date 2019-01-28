import { GName } from "./names";
import { Elem, showElem } from "./elems";
import { cloneMap } from "./util";

type El = Elem<GName>;
type ElType = El['tag'];
type IxMap = { [key in ElType]: Map<GName, number> };
type StackFrame = { type: ElType, name: GName, index: number | undefined };

export class Context {

  constructor(
    private readonly ctx: El[] = [],
    private readonly ix: IxMap = {
      CTVar: new Map(),
      CTMeta: new Map(),
      CVar: new Map(),
      CMarker: new Map(),
    },
    private readonly stack: StackFrame[] = [],
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

  enter(el: El): void {
    this.stack.push({
      type: el.tag,
      name: el.name,
      index: this.ix[el.tag].get(el.name),
    });
    this.add(el);
  }
  leave(): void {
    if (this.stack.length > 0) {
      const top = this.stack.pop() as StackFrame;
      if (typeof top.index === 'undefined') {
        this.ix[top.type].delete(top.name);
      } else {
        this.ix[top.type].set(top.name, top.index);
      }
    }
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

}
