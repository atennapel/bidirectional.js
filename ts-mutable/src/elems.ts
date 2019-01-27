import { impossible } from "./util";

export type Elem
  = CTVar
  | CTMeta
  | CVar
  | CMarker;

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
