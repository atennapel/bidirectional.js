// generated name
export class GName {

  constructor(
    readonly name: string,
    readonly index: number,
  ) {}

  toString(): string {
    return `${this.name}\$${this.index}`;
  }

}

export class GNameStore {
  
  constructor(
    readonly map: Map<string, number> = new Map(),
  ) {}

  fresh(name: string | GName): GName {
    const n = typeof name === 'string' ? name : name.name;
    const i = this.map.get(n) || 0;
    this.map.set(n, i + 1);
    return new GName(n, i);
  }

  reset() {
    this.map.clear();
  }

}
