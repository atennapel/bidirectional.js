import { Type } from './types';

export abstract class Expr {
	abstract subst(id: string, expr: Expr): Expr;
}

export class EVar extends Expr {
	readonly name : string
	constructor(name: string) {
		super();
		this.name = name;
	}

	public toString() {
		return this.name;
	}

	public subst(id: string, expr: Expr): Expr {
		return this.name === id? expr: this;
	}
}
export const evar = (name: string) => new EVar(name);

export class EUnit extends Expr {
	constructor() {
		super();
	}

	public toString() {
		return '()';
	}

	public subst(id: string, expr: Expr) {
		return this;
	}
}
export const eunit = new EUnit();

export class ELam extends Expr {
	readonly arg : string
	readonly body : Expr
	constructor(arg: string, body: Expr) {
		super();
		this.arg = arg;
		this.body = body;
	}

	public toString() {
		return `(\\${this.arg} -> ${this.body})`;
	}

	public subst(id: string, expr: Expr) {
		return this.arg === id? this: new ELam(this.arg, this.body.subst(id, expr));
	}
}
export const elam = (arg: string, body: Expr) => new ELam(arg, body);
export const elams = (args: string[], body: Expr) => {
	if(args.length < 1)
		throw new Error('Not enough arguments for elams');
	return args.reduceRight((x, y) => elam(y, x), body);
};

export class EApp extends Expr {
	readonly left : Expr
	readonly right : Expr
	constructor(left: Expr, right: Expr) {
		super();
		this.left = left;
		this.right = right;
	}

	public toString() {
		return `(${this.left} ${this.right})`;
	}

	public subst(id: string, expr: Expr) {
		return new EApp(this.left.subst(id, expr), this.right.subst(id, expr));
	}
}
export const eapp = (left: Expr, right: Expr) => new EApp(left, right);
export const eapps = (es: Expr[]) => {
	if(es.length < 2)
		throw new Error('Not enough arguments for elams');
	return es.reduce(eapp);
};

export class EAnno extends Expr {
	readonly expr : Expr
	readonly type : Type
	constructor(expr: Expr, type: Type) {
		super();
		this.expr = expr;
		this.type = type;
	}

	public toString() {
		return `(${this.expr} : ${this.type})`;
	}

	public subst(id: string, expr: Expr) {
		return new EAnno(this.expr.subst(id, expr), this.type);
	}
}
export const eanno = (expr: Expr, type: Type) => new EAnno(expr, type);
