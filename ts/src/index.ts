import {
	typeid,
	tunit,
	tvar,
	texists,
	tfuns,
	tforalls,
} from './types';
import {
	evar,
	eunit,
	elams,
	eapps,
	eanno,
} from './exprs';
import { infer } from './typechecker';
import { context, cvar } from './context';

const v0 = typeid(0);
const v1 = typeid(1);
const v2 = typeid(2);

const c = context([]);

const V = evar;
const U = eunit;
const L = elams;
const A = eapps;
const N = eanno;

const eid = N(L(['x'], V('x')), tforalls([v0], tfuns([tvar(v0), tvar(v0)])));
console.log(`${eid} : ${infer(eid, c)}`);

const ididunit = A([L(['id'], A([V('id'), V('id'), U])), eid]);
console.log(`${ididunit} : ${infer(ididunit, c)}`);

const idunit = A([L(['id'], A([V('id'), U])), eid]);
console.log(`${idunit} : ${infer(idunit, c)}`);

const idid = A([eid, eid]);
console.log(`${idid} : ${infer(idid, c)}`);
