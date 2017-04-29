import { Result } from './Result';

import {
	Type,
	TypeId,
	TVar,
	tvar,
	TExists,
	texists,
	TUnit,
	tunit,
	TFun,
	tfun,
	TForall,
} from './types';
import {
	Expr,
	EUnit,
	ELam,
	EVar,
	EAnno,
	EApp,
	evar,
} from './exprs';
import {
	Context,
	cforall,
	cmarker,
	cexists,
	cexistssolved,
	cvar,
} from './context';

type InferResult<T> = Result<TypeError, T>;
const ok = <T>(t: T) => Result.ok<TypeError, T>(t);
const err = <T>(m: string) => Result.err<TypeError, T>(new TypeError(m));

export class InferState {
	readonly current : TypeId;
	readonly currentVar : number;
	constructor(current: TypeId, currentVar: number) {
		this.current = current;
		this.currentVar = currentVar;
	}
	static empty() { return new InferState(TypeId.first(), 0) }
	public fresh(): [InferState, TypeId] {
		return [new InferState(this.current.next(), this.currentVar), this.current];
	}
	public freshVar(): [InferState, string] {
		return [new InferState(this.current, this.currentVar + 1), `\$${this.currentVar}`];
	}
}

const subtype = (state: InferState, context: Context, t1: Type, t2: Type)
	: InferResult<[InferState, Context]> => {

	if(!context.isWellformed())
		return err(`Ill-formed context in subtype: ${context}`);
	if(!t1.isWellformed(context))
		return err(`Ill-formed type in subtype: ${t1} with ${context}`);
	if(!t2.isWellformed(context))
		return err(`Ill-formed type in subtype: ${t2} with ${context}`);

	if(t1 instanceof TVar && t2 instanceof TVar && t1.id.equals(t2.id))
		return ok([state, context]);
	if(t1 instanceof TExists && t2 instanceof TExists && t1.id.equals(t2.id))
		return ok([state, context]);
	if(t1 instanceof TUnit && t2 instanceof TUnit)
		return ok([state, context]);
	if(t1 instanceof TFun && t2 instanceof TFun)
		return subtype(state, context, t2.left, t1.left)
			.then(([st1, c1]) => subtype(st1, c1, t1.right.apply(c1), t2.right.apply(c1)));
	if(t1 instanceof TForall) {
		const [st1, id] = state.fresh();
		return subtype(
			st1,
			context.add(cmarker(id), cexists(id)),
			t1.type.subst(t1.tvar, texists(id)),
			t2
		).then(([st2, c1]) => ok([st2, c1.dropFrom(cmarker(id))]));
	}
	if(t2 instanceof TForall)
		return subtype(
			state,
			context.add(cforall(t2.tvar)),
			t1,
			t2.type
		).then(([st1, c1]) => ok([st1, c1.dropFrom(cforall(t2.tvar))]));
	if(t1 instanceof TExists && !t2.free().contains(t1.id))
		return instantiateL(state, context, t1.id, t2);
	if(t2 instanceof TExists && !t1.free().contains(t2.id))
		return instantiateR(state, context, t1, t2.id);

	return err('Subtype failed on ' + t1 + ' and ' + t2 + ' with ' + context);
};

const solve = (context: Context, tvar: TypeId, type: Type): InferResult<Context> => {
	if(!type.isMono())
		return err(`Cannot solve with a polytype: ${tvar} = ${type}`);
	const [left, right] = context.split(cexists(tvar));
	if(type.isWellformed(left))
		return ok(Context.join(left, cexistssolved(tvar, type), right));
	return err(`Ill-formed type in solve: ${type}`);
};

const instantiateL = (state: InferState, context: Context, tv: TypeId, type: Type)
	:	InferResult<[InferState, Context]> => {

	if(!context.isWellformed())
		return err(`Ill-formed context in instantiateL: ${context}`);
	if(!texists(tv).isWellformed(context))
		return err(`Ill-formed type in instantiateL: ${texists(tv)} with ${context}`);
	if(!type.isWellformed(context))
		return err(`Ill-formed type in instantiateL: ${type} with ${context}`);

	return solve(context, tv, type)
		.then(c => ok([state, c]))
		.onErr(_ => {
			if(type instanceof TExists)
				return context.isOrdered(tv, type.id)?
					solve(context, type.id, texists(tv)).map(c => [state, c]):
					solve(context, tv, texists(type.id)).map(c => [state, c]);
			if(type instanceof TFun) {
				const [st1, alpha1] = state.fresh();
				const [st2, alpha2] = st1.fresh();
				return instantiateR(
					st2,
					context.insertAt(cexists(tv), [
						cexists(alpha2),
						cexists(alpha1),
						cexistssolved(tv, tfun(texists(alpha1), texists(alpha2))),
					]),
					type.left,
					alpha1
				).then(([st3, c1]) => instantiateL(st3, c1, alpha2, type.right.apply(c1)));
			}
			if(type instanceof TForall) {
				const [st1, beta] = state.fresh();
				return instantiateL(
					st1,
					context.add(cforall(beta)),
					tv,
					type.type.subst(type.tvar, tvar(beta))
				).map(([st2, c1]) => [st2, c1.dropFrom(cforall(beta))]);
			}
			return err(`instantiateL failed: ${context}`);
		});
};

const instantiateR = (state: InferState, context: Context, type: Type, tv: TypeId)
	: InferResult<[InferState, Context]> => {

	if(!context.isWellformed())
		return err(`Ill-formed context in instantiateR: ${context}`);
	if(!type.isWellformed(context))
		return err(`Ill-formed type in instantiateR: ${type} with ${context}`);
	if(!texists(tv).isWellformed(context))
		return err(`Ill-formed type in instantiateR: ${texists(tv)} with ${context}`);

	return solve(context, tv, type)
		.then(c => ok([state, c]))
		.onErr(_ => {
			if(type instanceof TExists)
				return context.isOrdered(tv, type.id)?
					solve(context, type.id, texists(tv)).map(c => [state, c]):
					solve(context, tv, texists(type.id)).map(c => [state, c]);
			if(type instanceof TFun) {
				const [st1, alpha1] = state.fresh();
				const [st2, alpha2] = st1.fresh();
				return instantiateL(
					st2,
					context.insertAt(cexists(tv), [
						cexists(alpha2),
						cexists(alpha1),
						cexistssolved(tv, tfun(texists(alpha1), texists(alpha2))),
					]),
					alpha1,
					type.left
				).then(([st3, c1]) => instantiateR(st3, c1, type.right.apply(c1), alpha2));
			}
			if(type instanceof TForall) {
				const [st1, beta] = state.fresh();
				return instantiateR(
					st1,
					context.add(cmarker(beta), cexists(beta)),
					type.type.subst(type.tvar, texists(beta)),
					tv
				).map(([st2, c1]) => [st2, c1.dropFrom(cmarker(beta))]);
			}
			return err(`instantiateL failed: ${context}`);
		});
};

const typecheck = (state: InferState, context: Context, expr: Expr, type: Type)
	: InferResult<[InferState, Context]> => {
	// console.log(`typecheck ${expr} ${type} ${context}`);

	if(!context.isWellformed())
		return err(`Ill-formed context in typecheck: ${context}`);
	if(!type.isWellformed(context))
		return err(`Ill-formed type in typecheck: ${type} with ${context}`);

	if(expr instanceof EUnit && type instanceof TUnit)
		return ok([state, context]);
	if(type instanceof TForall) {
		const [st1, tv] = state.fresh();
		return typecheck(
			st1,
			context.add(cforall(tv)),
			expr,
			type.type.subst(type.tvar, tvar(tv))
		).map(([st1, c]) => [st1, c.dropFrom(cforall(tv))]);
	}
	if(expr instanceof ELam && type instanceof TFun) {
		const [st1, x] = state.freshVar();
		return typecheck(
			st1,
			context.add(cvar(x, type.left)),
			expr.body.subst(expr.arg, evar(x)),
			type.right
		).map(([st2, c]) => [st2, c.dropFrom(cvar(x, type.left))]);
	}
	return typesynth(state, context, expr)
		.then(([st1, t, c]) => subtype(st1, c, t.apply(c), type.apply(c)));
};

const typesynth = (state: InferState, context: Context, expr: Expr)
	: InferResult<[InferState, Type, Context]> => {
	// console.log(`typesynth ${expr} ${context}`);

	if(!context.isWellformed())
		return err(`Ill-formed context in typesynth: ${context}`);

	if(expr instanceof EVar) {
		const type = context.getType(expr.name);
		if(!type) return err(`Not in scope: ${expr.name}`);
		return ok([state, type, context]);
	}
	if(expr instanceof EAnno)
		return typecheck(state, context, expr.expr, expr.type)
			.map(([st1, c]) => [st1, expr.type, c]);
	if(expr instanceof EApp)
		return typesynth(state, context, expr.left)
			.then(([st1, t, c]) => typeapplysynth(st1, c, t.apply(c), expr.right));
	if(expr instanceof ELam) {
		const [st1, x] = state.freshVar();
		const [st2, alpha] = st1.fresh();
		const [st3, beta] = st2.fresh();
		return typecheck(
			st3,
			context.add(
				cexists(alpha),
				cexists(beta),
				cvar(x, texists(alpha))
			),
			expr.body.subst(expr.arg, evar(x)),
			texists(beta)
		).map(([st, c]) => [st, tfun(texists(alpha), texists(beta)), c] as [InferState, Type, Context]);
	}
	if(expr instanceof EUnit)
		return ok([state, tunit, context]);

	return err(`typesynth failed for ${expr}`);
};

const typeapplysynth = (state: InferState, context: Context, type: Type, expr: Expr)
	: InferResult<[InferState, Type, Context]> => {
	// console.log(`typeapplysynth ${type} ${expr} ${context}`);

	if(!context.isWellformed())
		return err(`Ill-formed context in typeapplysynth: ${context}`);
	if(!type.isWellformed(context))
		return err(`Ill-formed type in typeapplysynth: ${type} with ${context}`);

	if(type instanceof TForall) {
		const [st1, alpha] = state.fresh();
		return typeapplysynth(
			st1,
			context.add(cexists(alpha)),
			type.type.subst(type.tvar, texists(alpha)),
			expr
		);
	}
	if(type instanceof TExists) {
		const [st1, alpha1] = state.fresh();
		const [st2, alpha2] = st1.fresh();
		return typecheck(
			st2,
			context.insertAt(cexists(type.id), [
				cexists(alpha2),
				cexists(alpha1),
				cexistssolved(type.id, tfun(texists(alpha1), texists(alpha2)))
			]),
			expr,
			texists(alpha1)
		).map(([st, c]) => [st, texists(alpha2), c] as [InferState, Type, Context]);
	}
	if(type instanceof TFun)
		return typecheck(state, context, expr, type.left)
			.map(([st, c]) => [st, type.right, c]);

	return err(`typeapplysynth failed for ${type} and ${expr}`);
};

export const infer = (expr: Expr, context_?: Context, state_?: InferState)
	: InferResult<Type> => {
	const context = context_ || Context.empty();
	const state = state_ || InferState.empty();
	return typesynth(state, context, expr)
		.map(([_, t, c]) => t.apply(c));
};
