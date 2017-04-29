import { clone } from './utils';
import Set from './Set';

type InternalMap<K, T> = {[key: string]: T};
export type KVPair<K, V> = [K, V];

export default class Map<K extends { hash : string }, V> {
  imap: InternalMap<K, V>;
  constructor(map: InternalMap<K, V>) {
    this.imap = map;
  }

  static from<K extends { hash : string }, V>(pairs: KVPair<K, V>[]) {
    let map: InternalMap<K, V> = {};
    for(let i = 0, l = pairs.length; i < l; i++)
      map[pairs[i][0].hash] = pairs[i][1];
    return new Map<K, V>(map);
  }
  static of<K extends { hash : string }, V>(...pairs: KVPair<K, V>[]) {
    return Map.from(pairs);
  }
  static empty<K extends { hash : string }, V>(): Map<K, V> { return Map.of<K, V>() }

  keys(): string[] { return Object.keys(this.imap) }
  vals(): V[] { return this.keys().map(k => this.imap[k]) }

  get(key: K): V | null { return this.imap[key.hash] }
  getOr(key: K, def: V): V { return this.imap[key.hash] || def }
  contains(key: K): boolean { return !!this.get(key)}

  toString(): string {
    return `{${this.keys().map(k => `${k}: ${this.imap[k]}`).join(', ')}}`;
  }

  map(fn: (val: V) => V) {
    let n: InternalMap<K, V> = {};
    for(let k in this.imap) n[k] = fn(this.imap[k]);
    return new Map<K, V>(n);
  }

  union(other: Map<K, V>): Map<K, V> {
    let n: InternalMap<K, V> = {};
    for(let k in this.imap) n[k] = this.imap[k];
    for(let k in other.imap) n[k] = other.imap[k];
    return new Map<K, V>(n);
  }
  removeKeysArray(keys: K[]) {
    let n: InternalMap<K, V> = clone(this.imap);
    for(let i = 0, l = keys.length; i < l; i++)
      delete n[keys[i].hash];
    return new Map<K, V>(n);
  }
  removeKeys(...keys: K[]) {
    return this.removeKeysArray(keys);
  }
  removeKey(k: K) {
    return this.removeKeys(k);
  }
  removeKeySet(ks: Set<K>) {
    return this.removeKeysArray(ks.vals());
  }
}
