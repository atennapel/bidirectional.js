(function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const elems_1 = require("./elems");
const inferctx_1 = require("./inferctx");
class Context {
    constructor(ctx = []) {
        this.ctx = ctx;
    }
    toString() {
        return `[${this.ctx.map(elems_1.showElem).join(', ')}]`;
    }
    clone() {
        const ctx = this.ctx.slice();
        return new Context(ctx);
    }
    addAll(es) {
        for (let i = 0, l = es.length; i < l; i++)
            this.ctx.push(es[i]);
        return this;
    }
    add(...es) {
        return this.addAll(es);
    }
    append(c) {
        return this.addAll(c.ctx);
    }
    indexOf(ty, name) {
        const a = this.ctx;
        const l = a.length;
        for (let i = 0; i < l; i++) {
            const c = a[i];
            if (c.tag === ty && c.name === name)
                return i;
        }
        return -1;
    }
    contains(ty, name) {
        return this.indexOf(ty, name) >= 0;
    }
    lookup(ty, name) {
        return (this.ctx[this.indexOf(ty, name)] || null);
    }
    pop() {
        return this.ctx.pop() || null;
    }
    split(ty, name) {
        const i = this.indexOf(ty, name);
        if (i < 0)
            return [];
        const ret = this.ctx.splice(i);
        ret.shift();
        return ret;
    }
    replace(ty, name, es) {
        const right = this.split(ty, name);
        this.addAll(es);
        this.addAll(right);
        return this;
    }
    isComplete() {
        const a = this.ctx;
        const l = a.length;
        for (let i = 0; i < l; i++) {
            const c = a[i];
            if (c.tag === 'CTMeta' && !c.type)
                return false;
        }
        return true;
    }
    enter(...es) {
        const m = inferctx_1.namestore.fresh('m');
        this.add(elems_1.CMarker(m));
        this.addAll(es);
        return m;
    }
    leave(m) {
        this.split('CMarker', m);
    }
    leaveWithUnsolved(m) {
        const ret = this.split('CMarker', m);
        const ns = [];
        for (let i = 0, l = ret.length; i < l; i++) {
            const c = ret[i];
            if (elems_1.isCTMeta(c) && !c.type)
                ns.push(c.name);
        }
        return ns;
    }
}
exports.Context = Context;

},{"./elems":2,"./inferctx":4}],2:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const util_1 = require("./util");
const types_1 = require("./types");
exports.CTVar = (name) => ({ tag: 'CTVar', name });
exports.isCTVar = (elem) => elem.tag === 'CTVar';
exports.CTMeta = (name, type = null) => ({ tag: 'CTMeta', name, type });
exports.isCTMeta = (elem) => elem.tag === 'CTMeta';
exports.CVar = (name, type) => ({ tag: 'CVar', name, type });
exports.isCVar = (elem) => elem.tag === 'CVar';
exports.CMarker = (name) => ({ tag: 'CMarker', name });
exports.isCMarker = (elem) => elem.tag === 'CMarker';
exports.showElem = (elem) => {
    if (exports.isCTVar(elem))
        return `${elem.name}`;
    if (exports.isCTMeta(elem))
        return `?${elem.name}${elem.type ? ` = ${types_1.showType(elem.type)}` : ''}`;
    if (exports.isCVar(elem))
        return `${elem.name} : ${types_1.showType(elem.type)}`;
    if (exports.isCMarker(elem))
        return `|${elem.name}`;
    return util_1.impossible('showElem');
};

},{"./types":8,"./util":9}],3:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const util_1 = require("./util");
const types_1 = require("./types");
exports.Var = (name) => ({ tag: 'Var', name });
exports.isVar = (expr) => expr.tag === 'Var';
exports.App = (left, right) => ({ tag: 'App', left, right });
exports.isApp = (expr) => expr.tag === 'App';
exports.Abs = (name, expr) => ({ tag: 'Abs', name, expr });
exports.isAbs = (expr) => expr.tag === 'Abs';
exports.Anno = (expr, type) => ({ tag: 'Anno', expr, type });
exports.isAnno = (expr) => expr.tag === 'Anno';
exports.showExpr = (expr) => {
    if (exports.isVar(expr))
        return `${expr.name}`;
    if (exports.isApp(expr))
        return `(${exports.showExpr(expr.left)} ${exports.showExpr(expr.right)})`;
    if (exports.isAbs(expr))
        return `(\\${expr.name}. ${exports.showExpr(expr.expr)})`;
    if (exports.isAnno(expr))
        return `(${exports.showExpr(expr.expr)} ${types_1.showType(expr.type)})`;
    return util_1.impossible('showExpr');
};
exports.substVar = (expr, v, s) => {
    if (exports.isVar(expr))
        return expr.name === v ? s : expr;
    if (exports.isApp(expr)) {
        const left = exports.substVar(expr.left, v, s);
        const right = exports.substVar(expr.right, v, s);
        return expr.left === left && expr.right === right ? expr : exports.App(left, right);
    }
    if (exports.isAbs(expr)) {
        if (expr.name === v)
            return expr;
        const body = exports.substVar(expr.expr, v, s);
        return expr.expr === body ? expr : exports.Abs(expr.name, body);
    }
    if (exports.isAnno(expr)) {
        const body = exports.substVar(expr.expr, v, s);
        return expr.expr === body ? expr : exports.Anno(body, expr.type);
    }
    return util_1.impossible('substVar');
};
exports.openAbs = (a, s) => exports.substVar(a.expr, a.name, s);

},{"./types":8,"./util":9}],4:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const context_1 = require("./context");
const names_1 = require("./names");
const types_1 = require("./types");
const util_1 = require("./util");
exports.context = new context_1.Context();
exports.namestore = new names_1.GNameStore();
class InferError extends Error {
    constructor(msg) { super(msg); }
}
exports.InferError = InferError;
exports.infererr = (msg) => { throw new InferError(msg); };
const ctxstack = [];
exports.store = () => { ctxstack.push(exports.context.clone()); };
exports.restore = () => { exports.context = ctxstack.pop() || exports.context; };
exports.discard = () => { ctxstack.pop(); };
exports.apply = (type, ctx = exports.context) => {
    if (types_1.isTVar(type))
        return type;
    if (types_1.isTMeta(type)) {
        const t = ctx.lookup('CTMeta', type.name);
        return t && t.type ? exports.apply(t.type, ctx) : type;
    }
    if (types_1.isTFun(type)) {
        const left = exports.apply(type.left, ctx);
        const right = exports.apply(type.right, ctx);
        return type.left === left && type.right === right ? type : types_1.TFun(left, right);
    }
    if (types_1.isTForall(type)) {
        const body = exports.apply(type.type, ctx);
        return type.type === body ? type : types_1.TForall(type.name, body);
    }
    return util_1.impossible('apply');
};

},{"./context":1,"./names":6,"./types":8,"./util":9}],5:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const exprs_1 = require("./exprs");
const types_1 = require("./types");
const inferctx_1 = require("./inferctx");
const wellformedness_1 = require("./wellformedness");
const subsumption_1 = require("./subsumption");
const elems_1 = require("./elems");
const generalize = (unsolved, type) => {
    const ns = types_1.unsolvedInType(unsolved, type);
    const m = new Map();
    for (let i = 0, l = ns.length; i < l; i++) {
        const x = ns[i];
        const y = inferctx_1.namestore.fresh(x);
        m.set(x, types_1.TVar(y));
    }
    let c = types_1.substTMetas(type, m);
    for (let i = ns.length - 1; i >= 0; i--)
        c = types_1.TForall(m.get(ns[i]).name, c);
    return c;
};
const generalizeFrom = (marker, type) => generalize(inferctx_1.context.leaveWithUnsolved(marker), type);
const typesynth = (expr) => {
    if (exprs_1.isVar(expr)) {
        const x = inferctx_1.context.lookup('CVar', expr.name);
        if (!x)
            return inferctx_1.infererr(`undefined var ${expr.name}`);
        return x.type;
    }
    if (exprs_1.isAbs(expr)) {
        const x = inferctx_1.namestore.fresh(expr.name);
        const a = inferctx_1.namestore.fresh(expr.name);
        const b = inferctx_1.namestore.fresh(expr.name);
        const ta = types_1.TMeta(a);
        const tb = types_1.TMeta(b);
        const m = inferctx_1.context.enter(elems_1.CTMeta(a), elems_1.CTMeta(b), elems_1.CVar(x, ta));
        typecheck(exprs_1.openAbs(expr, exprs_1.Var(x)), tb);
        const ty = inferctx_1.apply(types_1.TFun(ta, tb));
        return generalizeFrom(m, ty);
    }
    if (exprs_1.isApp(expr)) {
        const left = typesynth(expr.left);
        return typeappsynth(inferctx_1.apply(left), expr.right);
    }
    if (exprs_1.isAnno(expr)) {
        const ty = expr.type;
        wellformedness_1.wfType(ty);
        typecheck(expr.expr, ty);
        return ty;
    }
    return inferctx_1.infererr(`cannot synth: ${exprs_1.showExpr(expr)}`);
};
const typecheck = (expr, type) => {
    if (types_1.isTForall(type)) {
        const x = inferctx_1.namestore.fresh(type.name);
        const m = inferctx_1.context.enter(elems_1.CTVar(x));
        typecheck(expr, types_1.openTForall(type, types_1.TVar(x)));
        inferctx_1.context.leave(m);
        return;
    }
    if (exprs_1.isAbs(expr) && types_1.isTFun(type)) {
        const x = inferctx_1.namestore.fresh(expr.name);
        const m = inferctx_1.context.enter(elems_1.CVar(x, type.left));
        typecheck(exprs_1.openAbs(expr, exprs_1.Var(x)), type.right);
        inferctx_1.context.leave(m);
        return;
    }
    const ty = typesynth(expr);
    subsumption_1.subsume(inferctx_1.apply(ty), inferctx_1.apply(type));
};
const typeappsynth = (type, expr) => {
    if (types_1.isTForall(type)) {
        const x = inferctx_1.namestore.fresh(type.name);
        inferctx_1.context.add(elems_1.CTMeta(x));
        return typeappsynth(types_1.openTForall(type, types_1.TMeta(x)), expr);
    }
    if (types_1.isTMeta(type)) {
        const x = type.name;
        const a = inferctx_1.namestore.fresh(x);
        const b = inferctx_1.namestore.fresh(x);
        const ta = types_1.TMeta(a);
        const tb = types_1.TMeta(b);
        inferctx_1.context.replace('CTMeta', x, [
            elems_1.CTMeta(b),
            elems_1.CTMeta(a),
            elems_1.CTMeta(x, types_1.TFun(ta, tb)),
        ]);
        typecheck(expr, ta);
        return tb;
    }
    if (types_1.isTFun(type)) {
        typecheck(expr, type.left);
        return type.right;
    }
    return inferctx_1.infererr(`cannot typeappsynth: ${types_1.showType(type)} @ ${exprs_1.showExpr(expr)}`);
};
exports.infer = (expr) => {
    inferctx_1.namestore.reset();
    wellformedness_1.wfContext();
    const m = inferctx_1.context.enter();
    const ty = generalizeFrom(m, inferctx_1.apply(typesynth(expr)));
    if (!inferctx_1.context.isComplete())
        return inferctx_1.infererr(`incomplete context`);
    return ty;
};

},{"./elems":2,"./exprs":3,"./inferctx":4,"./subsumption":7,"./types":8,"./wellformedness":11}],6:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
// generated name
class GName {
    constructor(name, index) {
        this.name = name;
        this.index = index;
    }
    toString() {
        return `${this.name}\$${this.index}`;
    }
}
exports.GName = GName;
class GNameStore {
    constructor(map = new Map()) {
        this.map = map;
    }
    fresh(name) {
        const n = typeof name === 'string' ? name : name.name;
        const i = this.map.get(n) || 0;
        this.map.set(n, i + 1);
        return new GName(n, i);
    }
    reset() {
        this.map.clear();
    }
}
exports.GNameStore = GNameStore;

},{}],7:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const types_1 = require("./types");
const inferctx_1 = require("./inferctx");
const elems_1 = require("./elems");
const wellformedness_1 = require("./wellformedness");
const solve = (x, type) => {
    if (!types_1.isMono(type))
        return inferctx_1.infererr(`cannot solve with polytype: ${types_1.showType(x)} := ${types_1.showType(type)}`);
    const right = inferctx_1.context.split('CTMeta', x.name);
    wellformedness_1.wfType(type);
    inferctx_1.context.add(elems_1.CTMeta(x.name, type));
    inferctx_1.context.addAll(right);
};
const instL = (x, type) => {
    inferctx_1.store();
    try {
        solve(x, type);
        inferctx_1.discard();
    }
    catch (err) {
        if (!(err instanceof inferctx_1.InferError))
            throw err;
        inferctx_1.restore();
        if (types_1.isTMeta(type))
            return solve(type, x);
        if (types_1.isTFun(type)) {
            const y = x.name;
            const a = inferctx_1.namestore.fresh(y);
            const b = inferctx_1.namestore.fresh(y);
            const ta = types_1.TMeta(a);
            const tb = types_1.TMeta(b);
            inferctx_1.context.replace('CTMeta', y, [
                elems_1.CTMeta(b),
                elems_1.CTMeta(a),
                elems_1.CTMeta(y, types_1.TFun(ta, tb)),
            ]);
            instR(type.left, ta);
            instL(tb, inferctx_1.apply(type.right));
            return;
        }
        if (types_1.isTForall(type)) {
            const y = inferctx_1.namestore.fresh(type.name);
            const m = inferctx_1.context.enter(elems_1.CTVar(y));
            instL(x, types_1.openTForall(type, types_1.TVar(y)));
            inferctx_1.context.leave(m);
            return;
        }
        return inferctx_1.infererr(`instL failed: ${types_1.showType(x)} := ${types_1.showType(type)}`);
    }
};
const instR = (type, x) => {
    inferctx_1.store();
    try {
        solve(x, type);
        inferctx_1.discard();
    }
    catch (err) {
        if (!(err instanceof inferctx_1.InferError))
            throw err;
        inferctx_1.restore();
        if (types_1.isTMeta(type))
            return solve(type, x);
        if (types_1.isTFun(type)) {
            const y = x.name;
            const a = inferctx_1.namestore.fresh(y);
            const b = inferctx_1.namestore.fresh(y);
            const ta = types_1.TMeta(a);
            const tb = types_1.TMeta(b);
            inferctx_1.context.replace('CTMeta', y, [
                elems_1.CTMeta(b),
                elems_1.CTMeta(a),
                elems_1.CTMeta(y, types_1.TFun(ta, tb)),
            ]);
            instL(ta, type.left);
            instR(inferctx_1.apply(type.right), tb);
            return;
        }
        if (types_1.isTForall(type)) {
            const y = inferctx_1.namestore.fresh(type.name);
            const m = inferctx_1.context.enter(elems_1.CTMeta(y));
            instR(types_1.openTForall(type, types_1.TMeta(y)), x);
            inferctx_1.context.leave(m);
            return;
        }
        return inferctx_1.infererr(`instR failed: ${types_1.showType(x)} := ${types_1.showType(type)}`);
    }
};
exports.subsume = (a, b) => {
    if (a === b)
        return;
    if (types_1.isTVar(a) && types_1.isTVar(b) && a.name === b.name)
        return;
    if (types_1.isTMeta(a) && types_1.isTMeta(b) && a.name === b.name)
        return;
    if (types_1.isTFun(a) && types_1.isTFun(b)) {
        exports.subsume(b.left, a.left);
        exports.subsume(inferctx_1.apply(a.right), inferctx_1.apply(b.right));
        return;
    }
    if (types_1.isTForall(a)) {
        const x = inferctx_1.namestore.fresh(a.name);
        const m = inferctx_1.context.enter(elems_1.CTMeta(x));
        exports.subsume(types_1.openTForall(a, types_1.TMeta(x)), b);
        inferctx_1.context.leave(m);
        return;
    }
    if (types_1.isTForall(b)) {
        const x = inferctx_1.namestore.fresh(b.name);
        const m = inferctx_1.context.enter(elems_1.CTVar(x));
        exports.subsume(a, types_1.openTForall(b, types_1.TVar(x)));
        inferctx_1.context.leave(m);
        return;
    }
    if (types_1.isTMeta(a)) {
        if (types_1.containsTMeta(b, a.name))
            return inferctx_1.infererr(`occurs check L failed: ${types_1.showType(a)} in ${types_1.showType(b)}`);
        instL(a, b);
        return;
    }
    if (types_1.isTMeta(b)) {
        if (types_1.containsTMeta(a, b.name))
            return inferctx_1.infererr(`occurs check R failed: ${types_1.showType(b)} in ${types_1.showType(a)}`);
        instR(a, b);
        return;
    }
    return inferctx_1.infererr(`subsume failed: ${types_1.showType(a)} <: ${types_1.showType(b)}`);
};

},{"./elems":2,"./inferctx":4,"./types":8,"./wellformedness":11}],8:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const util_1 = require("./util");
exports.TVar = (name) => ({ tag: 'TVar', name });
exports.isTVar = (type) => type.tag === 'TVar';
exports.TMeta = (name) => ({ tag: 'TMeta', name });
exports.isTMeta = (type) => type.tag === 'TMeta';
exports.TFun = (left, right) => ({ tag: 'TFun', left, right });
exports.isTFun = (type) => type.tag === 'TFun';
exports.TForall = (name, type) => ({ tag: 'TForall', name, type });
exports.isTForall = (type) => type.tag === 'TForall';
exports.showType = (type) => {
    if (exports.isTVar(type))
        return `${type.name}`;
    if (exports.isTMeta(type))
        return `?${type.name}`;
    if (exports.isTFun(type))
        return `(${exports.showType(type.left)} -> ${exports.showType(type.right)})`;
    if (exports.isTForall(type))
        return `(forall ${type.name}. ${exports.showType(type.type)})`;
    return util_1.impossible('showType');
};
exports.substTVar = (type, x, s) => {
    if (exports.isTVar(type))
        return type.name === x ? s : type;
    if (exports.isTMeta(type))
        return type;
    if (exports.isTFun(type)) {
        const left = exports.substTVar(type.left, x, s);
        const right = exports.substTVar(type.right, x, s);
        return type.left === left && type.right === right ? type : exports.TFun(left, right);
    }
    if (exports.isTForall(type)) {
        if (type.name === x)
            return type;
        const body = exports.substTVar(type.type, x, s);
        return type.type === body ? type : exports.TForall(type.name, body);
    }
    return util_1.impossible('substTVar');
};
exports.openTForall = (forall, s) => exports.substTVar(forall.type, forall.name, s);
exports.containsTMeta = (type, m) => {
    if (exports.isTVar(type))
        return false;
    if (exports.isTMeta(type))
        return type.name === m;
    if (exports.isTFun(type))
        return exports.containsTMeta(type.left, m) || exports.containsTMeta(type.right, m);
    if (exports.isTForall(type))
        return exports.containsTMeta(type.type, m);
    return util_1.impossible('containsTMeta');
};
exports.isMono = (type) => {
    if (exports.isTVar(type))
        return true;
    if (exports.isTMeta(type))
        return true;
    if (exports.isTFun(type))
        return exports.isMono(type.left) && exports.isMono(type.right);
    if (exports.isTForall(type))
        return false;
    return util_1.impossible('isMono');
};
exports.substTMetas = (type, m) => {
    if (exports.isTVar(type))
        return type;
    if (exports.isTMeta(type))
        return m.get(type.name) || type;
    if (exports.isTFun(type)) {
        const left = exports.substTMetas(type.left, m);
        const right = exports.substTMetas(type.right, m);
        return type.left === left && type.right === right ? type : exports.TFun(left, right);
    }
    if (exports.isTForall(type)) {
        const body = exports.substTMetas(type.type, m);
        return type.type === body ? type : exports.TForall(type.name, body);
    }
    return util_1.impossible('substTMetas');
};
exports.unsolvedInType = (unsolved, type, ns = []) => {
    if (exports.isTVar(type))
        return ns;
    if (exports.isTMeta(type)) {
        const x = type.name;
        if (unsolved.indexOf(x) >= 0 && ns.indexOf(x) < 0)
            ns.push(x);
        return ns;
    }
    if (exports.isTFun(type)) {
        exports.unsolvedInType(unsolved, type.left, ns);
        return exports.unsolvedInType(unsolved, type.right, ns);
    }
    if (exports.isTForall(type))
        return exports.unsolvedInType(unsolved, type.type, ns);
    return util_1.impossible('unsolvedInType');
};

},{"./util":9}],9:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.impossible = (msg) => { throw new Error(`impossible: ${msg}`); };
exports.cloneMap = (map) => {
    const m = new Map();
    for (let k of map.keys())
        m.set(k, map.get(k));
    return m;
};

},{}],10:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const exprs_1 = require("./exprs");
const inference_1 = require("./inference");
const types_1 = require("./types");
const inferctx_1 = require("./inferctx");
const elems_1 = require("./elems");
const x = inferctx_1.namestore.fresh('x');
const y = inferctx_1.namestore.fresh('y');
const choose = inferctx_1.namestore.fresh('choose');
inferctx_1.context.add(elems_1.CVar(choose, types_1.TForall(x, types_1.TFun(types_1.TVar(x), types_1.TFun(types_1.TVar(x), types_1.TVar(x))))));
const expr = exprs_1.App(exprs_1.Var(choose), exprs_1.Abs(x, exprs_1.Var(x)));
console.log(exprs_1.showExpr(expr));
try {
    const type = inference_1.infer(expr);
    console.log(types_1.showType(type));
}
catch (err) {
    console.log('' + err);
}

},{"./elems":2,"./exprs":3,"./inferctx":4,"./inference":5,"./types":8}],11:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const types_1 = require("./types");
const util_1 = require("./util");
const inferctx_1 = require("./inferctx");
const elems_1 = require("./elems");
exports.wfType = (type) => {
    if (types_1.isTVar(type)) {
        if (!inferctx_1.context.contains('CTVar', type.name))
            inferctx_1.infererr(`undefined tvar ${type.name}`);
        return;
    }
    if (types_1.isTMeta(type)) {
        if (!inferctx_1.context.contains('CTMeta', type.name))
            inferctx_1.infererr(`undefined tmeta ?${type.name}`);
        return;
    }
    if (types_1.isTFun(type)) {
        exports.wfType(type.left);
        exports.wfType(type.right);
        return;
    }
    if (types_1.isTForall(type)) {
        const t = inferctx_1.namestore.fresh(type.name);
        const m = inferctx_1.context.enter(elems_1.CTVar(t));
        exports.wfType(types_1.openTForall(type, types_1.TVar(t)));
        inferctx_1.context.leave(m);
        return;
    }
    return util_1.impossible('wfType');
};
exports.wfElem = (elem) => {
    if (elems_1.isCTVar(elem)) {
        if (inferctx_1.context.contains('CTVar', elem.name))
            inferctx_1.infererr(`duplicate tvar ${elem.name}`);
        return;
    }
    if (elems_1.isCTMeta(elem)) {
        if (inferctx_1.context.contains('CTMeta', elem.name))
            inferctx_1.infererr(`duplicate tmeta ?${elem.name}`);
        return;
    }
    if (elems_1.isCVar(elem)) {
        if (inferctx_1.context.contains('CVar', elem.name))
            inferctx_1.infererr(`duplicate cvar ${elem.name}`);
        return;
    }
    if (elems_1.isCMarker(elem)) {
        if (inferctx_1.context.contains('CMarker', elem.name))
            inferctx_1.infererr(`duplicate cmarker |${elem.name}`);
        return;
    }
    ;
    return util_1.impossible('wfElem');
};
exports.wfContext = () => {
    inferctx_1.store();
    let elem = inferctx_1.context.pop();
    while (elem) {
        exports.wfElem(elem);
        elem = inferctx_1.context.pop();
    }
    inferctx_1.restore();
};

},{"./elems":2,"./inferctx":4,"./types":8,"./util":9}]},{},[10]);
