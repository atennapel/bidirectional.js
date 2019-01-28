import { GName } from "./names";
import { Type, isTForall, isTFun, isTMeta, isTVar, TVar, openTForall } from "./types";
import { impossible } from "./util";
import { context, infererr, namestore, store, restore } from "./inferctx";
import { CTVar, Elem, isCTVar, isCTMeta, isCVar, isCMarker } from "./elems";

export const wfType = (type: Type<GName>): void => {
  if (isTVar(type)) { if (!context.contains('CTVar', type.name)) infererr(`undefined tvar ${type.name}`) }
  if (isTMeta(type)) { if (!context.contains('CTMeta', type.name)) infererr(`undefined tmeta ?${type.name}`) }
  if (isTFun(type)) { wfType(type.left); wfType(type.right) }
  if (isTForall(type)) {
    const t = namestore.fresh(type.name);
    context.enter(CTVar(t));
    wfType(openTForall(type, TVar(t)));
    context.leave();
  }
  return impossible('wfType');
};

export const wfElem = (elem: Elem<GName>): void => {
  if (isCTVar(elem)) { if (context.contains('CTVar', elem.name)) infererr(`duplicate tvar ${elem.name}`) }
  if (isCTMeta(elem)) { if (context.contains('CTMeta', elem.name)) infererr(`duplicate tmeta ?${elem.name}`) }
  if (isCVar(elem)) { if (context.contains('CVar', elem.name)) infererr(`duplicate cvar ${elem.name}`) }
  if (isCMarker(elem)) { if (context.contains('CMarker', elem.name)) infererr(`duplicate cmarker |${elem.name}`) };
  return impossible('wfElem');
};

export const wfContext = (): void => {
  store();
  let elem: Elem<GName> | null = context.pop();
  while (elem) {
    wfElem(elem);
    elem = context.pop();
  }
  restore();
};
