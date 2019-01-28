import { impossible } from "./util";
import { Type, showType } from "./types";

export type Elem<N>
  = CTVar<N>
  | CTMeta<N>
  | CVar<N>
  | CMarker<N>;
export type ElemFromTag<N> = {
  CTVar: CTVar<N>;
  CTMeta: CTMeta<N>;
  CVar: CVar<N>;
  CMarker: CMarker<N>;
};

export interface CTVar<N> {
  readonly tag: 'CTVar';
  readonly name: N;
}
export const CTVar = <N>(name: N): CTVar<N> => ({ tag: 'CTVar', name });
export const isCTVar = <N>(elem: Elem<N>): elem is CTVar<N> => elem.tag === 'CTVar';

export interface CTMeta<N> {
  readonly tag: 'CTMeta';
  readonly name: N;
  readonly type: Type<N> | null;
}
export const CTMeta = <N>(name: N, type: Type<N> | null = null): CTMeta<N> =>
  ({ tag: 'CTMeta', name, type });
export const isCTMeta = <N>(elem: Elem<N>): elem is CTMeta<N> => elem.tag === 'CTMeta';

export interface CVar<N> {
  readonly tag: 'CVar';
  readonly name: N;
  readonly type: Type<N>;
}
export const CVar = <N>(name: N, type: Type<N>): CVar<N> => ({ tag: 'CVar', name, type });
export const isCVar = <N>(elem: Elem<N>): elem is CVar<N> => elem.tag === 'CVar';

export interface CMarker<N> {
  readonly tag: 'CMarker';
  readonly name: N;
}
export const CMarker = <N>(name: N): CMarker<N> => ({ tag: 'CMarker', name });
export const isCMarker = <N>(elem: Elem<N>): elem is CMarker<N> => elem.tag === 'CMarker';

export const showElem = <N>(elem: Elem<N>): string => {
  if (isCTVar(elem)) return `${elem.name}`;
  if (isCTMeta(elem)) return `?${elem.name}${elem.type ? ` = ${showType(elem.type)}` : ''}`;
  if (isCVar(elem)) return `${elem.name} : ${showType(elem.type)}`;
  if (isCMarker(elem)) return `|${elem.name}`;
  return impossible('showElem');
};
