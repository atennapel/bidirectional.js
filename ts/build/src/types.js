"use strict";
var __extends = (this && this.__extends) || (function () {
    var extendStatics = Object.setPrototypeOf ||
        ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
        function (d, b) { for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p]; };
    return function (d, b) {
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };
})();
exports.__esModule = true;
var Set_1 = require("./Set");
var context_1 = require("./context");
var TypeId = (function () {
    function TypeId(id) {
        this.id = id;
        this.hash = '' + id;
    }
    TypeId.first = function () { return new TypeId(0); };
    TypeId.prototype.toString = function () { return '' + this.id; };
    TypeId.prototype.equals = function (other) { return this.id === other.id; };
    TypeId.prototype.next = function () { return new TypeId(this.id + 1); };
    return TypeId;
}());
exports.TypeId = TypeId;
exports.typeid = function (id) { return new TypeId(id); };
var Type = (function () {
    function Type() {
    }
    return Type;
}());
exports.Type = Type;
exports.substs = function (s, t) {
    return s.reduce(function (t, s) { return t.subst(s[0], s[1]); }, t);
};
var TUnit = (function (_super) {
    __extends(TUnit, _super);
    function TUnit() {
        return _super.call(this) || this;
    }
    TUnit.prototype.toString = function () {
        return '()';
    };
    TUnit.prototype.equals = function (other) {
        return other instanceof TUnit;
    };
    TUnit.prototype.subst = function (id, type) {
        return this;
    };
    TUnit.prototype.free = function () {
        return Set_1["default"].empty();
    };
    TUnit.prototype.isMono = function () { return true; };
    TUnit.prototype.isWellformed = function (context) {
        return true;
    };
    TUnit.prototype.apply = function (context) {
        return this;
    };
    return TUnit;
}(Type));
exports.TUnit = TUnit;
exports.tunit = new TUnit();
var TVar = (function (_super) {
    __extends(TVar, _super);
    function TVar(id) {
        var _this = _super.call(this) || this;
        _this.id = id;
        return _this;
    }
    TVar.prototype.toString = function () {
        return "'" + this.id;
    };
    TVar.prototype.equals = function (other) {
        return other instanceof TVar && this.id.equals(other.id);
    };
    TVar.prototype.subst = function (id, type) {
        return this.id.equals(id) ? type : this;
    };
    TVar.prototype.free = function () {
        return Set_1["default"].of(this.id);
    };
    TVar.prototype.isMono = function () { return true; };
    TVar.prototype.isWellformed = function (context) {
        return context.contains(context_1.cforall(this.id));
    };
    TVar.prototype.apply = function (context) {
        return this;
    };
    return TVar;
}(Type));
exports.TVar = TVar;
exports.tvar = function (id) { return new TVar(id); };
var TExists = (function (_super) {
    __extends(TExists, _super);
    function TExists(id) {
        var _this = _super.call(this) || this;
        _this.id = id;
        return _this;
    }
    TExists.prototype.toString = function () {
        return "^" + this.id;
    };
    TExists.prototype.equals = function (other) {
        return other instanceof TExists && this.id.equals(other.id);
    };
    TExists.prototype.subst = function (id, type) {
        return this.id.equals(id) ? type : this;
    };
    TExists.prototype.free = function () {
        return Set_1["default"].of(this.id);
    };
    TExists.prototype.isMono = function () { return true; };
    TExists.prototype.isWellformed = function (context) {
        return context.containsExistential(this.id);
    };
    TExists.prototype.apply = function (context) {
        var type = context.getSolved(this.id);
        return type ? type.apply(context) : this;
    };
    return TExists;
}(Type));
exports.TExists = TExists;
exports.texists = function (id) { return new TExists(id); };
var TFun = (function (_super) {
    __extends(TFun, _super);
    function TFun(left, right) {
        var _this = _super.call(this) || this;
        _this.left = left;
        _this.right = right;
        return _this;
    }
    TFun.prototype.toString = function () {
        return "(" + this.left + " -> " + this.right + ")";
    };
    TFun.prototype.equals = function (other) {
        return other instanceof TFun && this.left.equals(other.left) && this.right.equals(other.right);
    };
    TFun.prototype.subst = function (id, type) {
        return new TFun(this.left.subst(id, type), this.right.subst(id, type));
    };
    TFun.prototype.free = function () {
        return this.left.free().union(this.right.free());
    };
    TFun.prototype.isMono = function () { return this.left.isMono() && this.right.isMono(); };
    TFun.prototype.isWellformed = function (context) {
        return this.left.isWellformed(context) && this.right.isWellformed(context);
    };
    TFun.prototype.apply = function (context) {
        return new TFun(this.left.apply(context), this.right.apply(context));
    };
    return TFun;
}(Type));
exports.TFun = TFun;
exports.tfun = function (left, right) { return new TFun(left, right); };
exports.tfuns = function (ts) {
    if (ts.length < 2)
        throw new Error('Not enough arguments for tarrs');
    return ts.reduceRight(function (x, y) { return exports.tfun(y, x); });
};
var TForall = (function (_super) {
    __extends(TForall, _super);
    function TForall(tvar, type) {
        var _this = _super.call(this) || this;
        _this.tvar = tvar;
        _this.type = type;
        return _this;
    }
    TForall.prototype.toString = function () {
        return "(forall " + this.tvar + " . " + this.type + ")";
    };
    TForall.prototype.equals = function (other) {
        return other instanceof TForall && this.tvar.equals(other.tvar) && this.type.equals(other.type);
    };
    TForall.prototype.subst = function (id, type) {
        return this.tvar.equals(id) ? this : new TForall(this.tvar, this.type.subst(id, type));
    };
    TForall.prototype.free = function () {
        return this.type.free().remove(this.tvar);
    };
    TForall.prototype.isMono = function () { return false; };
    TForall.prototype.isWellformed = function (context) {
        return this.type.isWellformed(context.add(context_1.cforall(this.tvar)));
    };
    TForall.prototype.apply = function (context) {
        return new TForall(this.tvar, this.type.apply(context));
    };
    return TForall;
}(Type));
exports.TForall = TForall;
exports.tforall = function (tvar, type) { return new TForall(tvar, type); };
exports.tforalls = function (tvars, type) {
    if (tvars.length < 1)
        throw new Error('Not enough arguments for tforalls');
    return tvars.reduceRight(function (x, y) { return exports.tforall(y, x); }, type);
};
