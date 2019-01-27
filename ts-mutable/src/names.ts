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
    readonly map: { [key: string]: number } = {},
  ) {}

  fresh(name: string | GName): GName {
    const n = typeof name === 'string' ? name : name.name;
    if (!this.map[n]) this.map[n] = 0;
    return new GName(n, this.map[n]++);
  }

}
