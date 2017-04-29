import Set from './Set';
import {
	Context,
	cforall,
	cexists,
} from './context';

export class TypeId {
	readonly id : number
	readonly hash : string
	constructor(id: number) {
		this.id = id;
		this.hash = '' + id;
	}
	static first() { return new TypeId(0) }
	public toString() { return '' + this.id }
	public equals(other: TypeId) { return this.id === other.id }
	public next(): TypeId { return new TypeId(this.id + 1) }
}
export const typeid = (id: number) => new TypeId(id);

export abstract class Type {
	abstract equals(other: Type): boolean;
	abstract subst(id: TypeId, type: Type): Type;
	abstract free(): Set<TypeId>;
	abstract isMono(): boolean;
	abstract isWellformed(context: Context): boolean;
	abstract apply(context: Context): Type;
}
export const substs = (s: [TypeId, Type][], t: Type) =>
	s.reduce((t, s) => t.subst(s[0], s[1]), t);

export class TUnit extends Type {
	constructor() {
		super();
	}

	public toString() {
		return '()';
	}
	public equals(other: Type): boolean {
		return other instanceof TUnit;
	}

	public subst(id: TypeId, type: Type) {
		return this;
	}
	public free() {
		return Set.empty<TypeId>();
	}
	public isMono() { return true }
	public isWellformed(context: Context): boolean {
		return true;
	}
	public apply(context: Context): Type {
		return this;
	}
}
export const tunit = new TUnit();

export class TVar extends Type {
	readonly id : TypeId;
	constructor(id: TypeId) {
		super();
		this.id = id;
	}

	public toString() {
		return `'${this.id}`;
	}
	public equals(other: Type): boolean {
		return other instanceof TVar && this.id.equals(other.id);
	}

	public subst(id: TypeId, type: Type): Type {
		return this.id.equals(id)? type: this;
	}
	public free() {
		return Set.of(this.id);
	}
	public isMono() { return true }
	public isWellformed(context: Context): boolean {
		return context.contains(cforall(this.id));
	}
	public apply(context: Context): Type {
		return this;
	}
}
export const tvar = (id: TypeId) => new TVar(id);

export class TExists extends Type {
	readonly id : TypeId;
	constructor(id: TypeId) {
		super();
		this.id = id;
	}

	public toString() {
		return `^${this.id}`;
	}
	public equals(other: Type): boolean {
		return other instanceof TExists && this.id.equals(other.id);
	}

	public subst(id: TypeId, type: Type): Type {
		return this.id.equals(id)? type: this;
	}
	public free() {
		return Set.of(this.id);
	}
	public isMono() { return true }
	public isWellformed(context: Context): boolean {
		return context.containsExistential(this.id);
	}
	public apply(context: Context): Type {
		const type = context.getSolved(this.id);
		return type? type.apply(context): this;
	}
}
export const texists = (id: TypeId) => new TExists(id);

export class TFun extends Type {
	readonly left : Type;
	readonly right : Type;
	constructor(left: Type, right: Type) {
		super();
		this.left = left;
		this.right = right;
	}

	public toString() {
		return `(${this.left} -> ${this.right})`;
	}
	public equals(other: Type): boolean {
		return other instanceof TFun && this.left.equals(other.left) && this.right.equals(other.right);
	}

	public subst(id: TypeId, type: Type): Type {
		return new TFun(this.left.subst(id, type), this.right.subst(id, type));
	}
	public free() {
		return this.left.free().union(this.right.free());
	}
	public isMono() { return this.left.isMono() && this.right.isMono() }
	public isWellformed(context: Context): boolean {
		return this.left.isWellformed(context) && this.right.isWellformed(context);
	}
	public apply(context: Context): Type {
		return new TFun(this.left.apply(context), this.right.apply(context));
	}
}
export const tfun = (left: Type, right: Type) => new TFun(left, right);
export const tfuns = (ts: Type[]) => {
	if(ts.length < 2) throw new Error('Not enough arguments for tarrs');
	return ts.reduceRight((x, y) => tfun(y, x));
};

export class TForall extends Type {
	readonly tvar : TypeId;
	readonly type : Type;
	constructor(tvar: TypeId, type: Type) {
		super();
		this.tvar = tvar;
		this.type = type;
	}

	public toString() {
		return `(forall ${this.tvar} . ${this.type})`;
	}
	public equals(other: Type): boolean {
		return other instanceof TForall && this.tvar.equals(other.tvar) && this.type.equals(other.type);
	}

	public subst(id: TypeId, type: Type): Type {
		return this.tvar.equals(id)? this: new TForall(this.tvar, this.type.subst(id, type));
	}
	public free() {
		return this.type.free().remove(this.tvar);
	}
	public isMono() { return false }
	public isWellformed(context: Context): boolean {
		return this.type.isWellformed(context.add(cforall(this.tvar)));
	}
	public apply(context: Context): Type {
		return new TForall(this.tvar, this.type.apply(context));
	}
}
export const tforall = (tvar: TypeId, type: Type) => new TForall(tvar, type);
export const tforalls = (tvars: TypeId[], type: Type) => {
	if(tvars.length < 1) throw new Error('Not enough arguments for tforalls');
	return tvars.reduceRight((x, y) => tforall(y, x), type);
}
