import { impossible } from "./util";

export type Type<N>
  = TVar<N>
  | TMeta<N>
  | TFun<N>
  | TForall<N>;

export interface TVar<N> {
  readonly tag: 'TVar';
  readonly name: N;
}
export const TVar = <N>(name: N): TVar<N> => ({ tag: 'TVar', name });
export const isTVar = <N>(type: Type<N>): type is TVar<N> => type.tag === 'TVar';

export interface TMeta<N> {
  readonly tag: 'TMeta';
  readonly name: N;
}
export const TMeta = <N>(name: N): TMeta<N> => ({ tag: 'TMeta', name });
export const isTMeta = <N>(type: Type<N>): type is TMeta<N> => type.tag === 'TMeta';

export interface TFun<N> {
  readonly tag: 'TFun';
  readonly left: Type<N>;
  readonly right: Type<N>;
}
export const TFun = <N>(left: Type<N>, right: Type<N>): TFun<N> =>
  ({ tag: 'TFun', left, right });
export const isTFun = <N>(type: Type<N>): type is TFun<N> => type.tag === 'TFun';

export interface TForall<N> {
  readonly tag: 'TForall';
  readonly name: N;
  readonly type: Type<N>;
}
export const TForall = <N>(name: N, type: Type<N>): TForall<N> =>
  ({ tag: 'TForall', name, type });
export const isTForall = <N>(type: Type<N>): type is TForall<N> => type.tag === 'TForall';

export const showType = <N>(type: Type<N>): string => {
  if (isTVar(type)) return `${type.name}`;
  if (isTMeta(type)) return `?${type.name}`;
  if (isTFun(type)) return `(${showType(type.left)} -> ${showType(type.right)}`;
  if (isTForall(type)) return `(forall ${type.name}. ${showType(type.type)})`;
  return impossible('showType');
};

export const substTVar = <N>(type: Type<N>, x: N, s: Type<N>): Type<N> => {
  if (isTVar(type)) return type.name === x ? s : type;
  if (isTMeta(type)) return type;
  if (isTFun(type)) {
    const left = substTVar(type.left, x, s);
    const right = substTVar(type.right, x, s);
    return type.left === left && type.right === right ? type : TFun(left, right);
  }
  if (isTForall(type)) {
    if (type.name === x) return type;
    const body = substTVar(type.type, x, s);
    return type.type === body ? type : TForall(type.name, body);
  }
  return impossible('substTVar');
};
export const openTForall = <N>(forall: TForall<N>, s: Type<N>): Type<N> =>
  substTVar(forall.type, forall.name, s);
