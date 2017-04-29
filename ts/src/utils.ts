export function clone<V>(o: {[key: string]: V}) {
  let n: {[key: string]: V} = {};
  for(let k in o) n[k] = o[k];
  return n;
}
