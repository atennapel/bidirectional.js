import { GName } from "./names";
import { Elem, showElem } from "./elems";

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
  ) {}

  toString(): string {
    return `[${this.ctx.map(showElem).join(', ')}]`;
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

}
