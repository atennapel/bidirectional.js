export abstract class Result<E, T> {
  constructor() {}
  static ok<E, T>(t: T) { return new Ok<E, T>(t) }
  static err<E, T>(e: E) { return new Err<E, T>(e) }
  abstract map<R>(fn: (val: T) => R): Result<E, R>;
  abstract then<R>(fn: (val: T) => Result<E, R>): Result<E, R>;
	abstract onErr<R>(fn: (err: E) => Result<E, R>): Result<E, R>;
}

export class Ok<E, T> extends Result<E, T> {
  val: T;
  constructor(val: T) {
    super();
    this.val = val;
  }
  toString() { return 'Ok(' + this.val + ')' }
  map<R>(fn: (val: T) => R) { return new Ok<E, R>(fn(this.val)) }
  then<R>(fn: (val: T) => Result<E, R>) { return fn(this.val) }
	onErr<R>(fn: (err: E) => Result<E, R>) { return this }
}

export class Err<E, T> extends Result<E, T> {
  val: E;
  constructor(val: E) {
    super();
    this.val = val;
  }
  toString() { return 'Err(' + this.val + ')' }
  map<R>(fn: (val: T) => R) { return this }
  then<R>(fn: (val: T) => Result<E, R>) { return this }
	onErr<R>(fn: (err: E) => Result<E, R>) { return fn(this.val) }
}
