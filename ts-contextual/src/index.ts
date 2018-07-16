import {
  str,
} from './names';
import {
  tvar,
  tex,
  tfuns,
  tforalls,
  showType,
} from './types';
import {
  vr,
  apps,
  abss,
  anno,
  showTerm,
} from './terms';
import {
  pure,
  err,
  bind,
} from './context';

const t = tforalls([str('a'), str('b')], tfuns([tvar(str('a')), tfuns([tex(str('a')), tex(str('b'))]), tvar(str('c'))]));
const tm = abss([str('a'), str('b'), str('c')], apps([vr(str('a')), vr(str('f')), apps([vr(str('b')), anno(vr(str('c')), tvar(str('x')))])]));
console.log(showType(t));
console.log(showTerm(tm));
