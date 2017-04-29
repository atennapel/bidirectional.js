import {
	Type,
	TypeId,
} from './types';

export abstract class ContextElem {
	abstract equals(other: ContextElem): boolean;
	abstract isComplete(): boolean;
	abstract isWellformed(context: Context): boolean;
}

export class CForall extends ContextElem {
	readonly id : TypeId
	constructor(id: TypeId) {
		super();
		this.id = id;
	}

	public toString() {
		return ''+this.id;
	}
	public equals(other: ContextElem): boolean {
		return other instanceof CForall && this.id.equals(other.id);
	}
	public isComplete(): boolean { return true }
	public isWellformed(context: Context): boolean {
		return !context.contains(this);
	}
}
export const cforall = (id: TypeId) => new CForall(id);

export class CVar extends ContextElem {
	readonly name : string
	readonly type : Type
	constructor(name: string, type: Type) {
		super();
		this.name = name;
		this.type = type;
	}

	public toString() {
		return `${this.name} : ${this.type}`;
	}
	public equals(other: ContextElem): boolean {
		return other instanceof CVar && this.name === other.name && this.type.equals(other.type);
	}
	public isComplete(): boolean { return true }
	public isWellformed(context: Context): boolean {
		return !context.containsVar(this.name) && this.type.isWellformed(context);
	}
}
export const cvar = (name: string, type: Type) => new CVar(name, type);

export class CExists extends ContextElem {
	readonly id : TypeId
	constructor(id : TypeId) {
		super();
		this.id = id;
	}
	
	public toString() {
		return ''+this.id;
	}
	public equals(other: ContextElem): boolean {
		return other instanceof CExists && this.id.equals(other.id);
	}
	public isComplete(): boolean { return false }
	public isWellformed(context: Context): boolean {
		return !context.containsExistential(this.id);
	}
}
export const cexists = (id: TypeId) => new CExists(id);

export class CExistsSolved extends ContextElem {
	readonly id : TypeId;
	readonly type : Type;
	constructor(id: TypeId, type: Type) {
		super();
		this.id = id;
		this.type = type;
	}
	
	public toString() {
		return `${this.id} = ${this.type}`;
	}
	public equals(other: ContextElem): boolean {
		return other instanceof CExistsSolved && this.id.equals(other.id) && this.type.equals(other.type);
	}
	public isComplete(): boolean { return true }
	public isWellformed(context: Context): boolean {
		return !context.containsExistential(this.id) && this.type.isWellformed(context);
	}
}
export const cexistssolved = (id: TypeId, type: Type) => new CExistsSolved(id, type);

export class CMarker extends ContextElem {
	readonly id : TypeId;
	constructor(id: TypeId) {
		super();
		this.id = id;
	}
	
	public toString() {
		return `^${this.id}`;
	}
	public equals(other: ContextElem): boolean {
		return other instanceof CMarker && this.id.equals(other.id);
	}
	public isComplete(): boolean { return true }
	public isWellformed(context: Context): boolean {
		return !context.contains(this) && !context.containsExistential(this.id);
	}
}
export const cmarker = (id: TypeId) => new CMarker(id);

export class Context {
	readonly elems : ContextElem[];
	constructor(elems: ContextElem[]) {
		this.elems = elems;
	}

	static empty() { return new Context([]) }
	static join(left: Context, elem: ContextElem, right: Context) {
		return new Context(left.elems.concat([elem].concat(right.elems)));
	}

	public toString() {
		return `Context[${this.elems.join(', ')}]`;
	}

	public indexOf(elem: ContextElem): number {
		for(let i = 0, a = this.elems, l = a.length; i < l; i++)
			if(elem.equals(a[i])) return i;
		return -1;
	}
	public contains(elem: ContextElem): boolean {
		return this.indexOf(elem) >= 0;
	}

	public indexOfExistential(id: TypeId): number {
		for(let i = 0, a = this.elems, l = a.length; i < l; i++) {
			const c = a[i];
			if((c instanceof CExists && c.id.equals(id))
				|| (c instanceof CExistsSolved && c.id.equals(id)))
				return i;
		}
		return -1;
	}
	public containsExistential(id: TypeId): boolean {
		return this.indexOfExistential(id) >= 0;
	}

	public indexOfVar(name: string): number {
		for(let i = 0, a = this.elems, l = a.length; i < l; i++) {
			const c = a[i];
			if(c instanceof CVar && c.name === name)
				return i;
		}
		return -1;
	}
	public containsVar(name: string): boolean {
		return this.indexOfVar(name) >= 0;
	}

	public getSolved(id: TypeId): Type | null {
		const i = this.indexOfExistential(id);
		if(i < 0) return null;
		const e = this.elems[i];
		return e instanceof CExistsSolved? e.type: null;
	}
	public getType(id: string): Type | null {
		const i = this.indexOfVar(id);
		if(i < 0) return null;
		const e = this.elems[i];
		return e instanceof CVar? e.type: null;
	}

	public isComplete(): boolean {
		for(let i = 0, a = this.elems, l = a.length; i < l; i++)
			if(!a[i].isComplete()) return false;
		return true;
	}
	public isWellformed(): boolean {
		const l = this.elems.length;
		if(l === 0) return true;
		const init = this.init();
		return init.isWellformed() && this.elems[l - 1].isWellformed(init);
	}

	public init(): Context {
		return new Context(this.elems.slice(0, -1));
	}
	public add(...elem: ContextElem[]): Context {
		return new Context(this.elems.concat(elem));
	}
	public dropFrom(e: ContextElem): Context {
		const i = this.indexOf(e);
		if(i < 0) return this;
		return new Context(this.elems.slice(0, i));
	}
	public split(e: ContextElem): [Context, Context] {
		const i = this.indexOf(e);
		if(i < 0) return [this, Context.empty()];
		return [
			new Context(this.elems.slice(0, i)),
			new Context(this.elems.slice(i + 1)),
		];
	}
	public isOrdered(id1: TypeId, id2: TypeId): boolean {
		return this.dropFrom(cexists(id2)).containsExistential(id1);
	}
	public insertAt(elem: ContextElem, elems: ContextElem[]): Context {
		const [left, right] = this.split(elem);
		return new Context(left.elems.concat(elems).concat(right.elems));
	}
}
export const context = (elems: ContextElem[]) => new Context(elems);
