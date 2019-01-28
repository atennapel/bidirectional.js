export const impossible = (msg: string) => { throw new Error(`impossible: ${msg}`) }

export const cloneMap = <K, V>(map: Map<K, V>): Map<K, V> => {
  const m = new Map<K, V>();
  for (let k of map.keys()) m.set(k, map.get(k) as V);
  return m;
};
