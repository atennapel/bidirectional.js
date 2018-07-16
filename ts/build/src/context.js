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
var ContextElem = (function () {
    function ContextElem() {
    }
    return ContextElem;
}());
exports.ContextElem = ContextElem;
var CForall = (function (_super) {
    __extends(CForall, _super);
    function CForall(id) {
        var _this = _super.call(this) || this;
        _this.id = id;
        return _this;
    }
    CForall.prototype.toString = function () {
        return '' + this.id;
    };
    CForall.prototype.equals = function (other) {
        return other instanceof CForall && this.id.equals(other.id);
    };
    CForall.prototype.isComplete = function () { return true; };
    CForall.prototype.isWellformed = function (context) {
        return !context.contains(this);
    };
    return CForall;
}(ContextElem));
exports.CForall = CForall;
exports.cforall = function (id) { return new CForall(id); };
var CVar = (function (_super) {
    __extends(CVar, _super);
    function CVar(name, type) {
        var _this = _super.call(this) || this;
        _this.name = name;
        _this.type = type;
        return _this;
    }
    CVar.prototype.toString = function () {
        return this.name + " : " + this.type;
    };
    CVar.prototype.equals = function (other) {
        return other instanceof CVar && this.name === other.name && this.type.equals(other.type);
    };
    CVar.prototype.isComplete = function () { return true; };
    CVar.prototype.isWellformed = function (context) {
        return !context.containsVar(this.name) && this.type.isWellformed(context);
    };
    return CVar;
}(ContextElem));
exports.CVar = CVar;
exports.cvar = function (name, type) { return new CVar(name, type); };
var CExists = (function (_super) {
    __extends(CExists, _super);
    function CExists(id) {
        var _this = _super.call(this) || this;
        _this.id = id;
        return _this;
    }
    CExists.prototype.toString = function () {
        return '' + this.id;
    };
    CExists.prototype.equals = function (other) {
        return other instanceof CExists && this.id.equals(other.id);
    };
    CExists.prototype.isComplete = function () { return false; };
    CExists.prototype.isWellformed = function (context) {
        return !context.containsExistential(this.id);
    };
    return CExists;
}(ContextElem));
exports.CExists = CExists;
exports.cexists = function (id) { return new CExists(id); };
var CExistsSolved = (function (_super) {
    __extends(CExistsSolved, _super);
    function CExistsSolved(id, type) {
        var _this = _super.call(this) || this;
        _this.id = id;
        _this.type = type;
        return _this;
    }
    CExistsSolved.prototype.toString = function () {
        return this.id + " = " + this.type;
    };
    CExistsSolved.prototype.equals = function (other) {
        return other instanceof CExistsSolved && this.id.equals(other.id) && this.type.equals(other.type);
    };
    CExistsSolved.prototype.isComplete = function () { return true; };
    CExistsSolved.prototype.isWellformed = function (context) {
        return !context.containsExistential(this.id) && this.type.isWellformed(context);
    };
    return CExistsSolved;
}(ContextElem));
exports.CExistsSolved = CExistsSolved;
exports.cexistssolved = function (id, type) { return new CExistsSolved(id, type); };
var CMarker = (function (_super) {
    __extends(CMarker, _super);
    function CMarker(id) {
        var _this = _super.call(this) || this;
        _this.id = id;
        return _this;
    }
    CMarker.prototype.toString = function () {
        return "^" + this.id;
    };
    CMarker.prototype.equals = function (other) {
        return other instanceof CMarker && this.id.equals(other.id);
    };
    CMarker.prototype.isComplete = function () { return true; };
    CMarker.prototype.isWellformed = function (context) {
        return !context.contains(this) && !context.containsExistential(this.id);
    };
    return CMarker;
}(ContextElem));
exports.CMarker = CMarker;
exports.cmarker = function (id) { return new CMarker(id); };
var Context = (function () {
    function Context(elems) {
        this.elems = elems;
    }
    Context.empty = function () { return new Context([]); };
    Context.join = function (left, elem, right) {
        return new Context(left.elems.concat([elem].concat(right.elems)));
    };
    Context.prototype.toString = function () {
        return "Context[" + this.elems.join(', ') + "]";
    };
    Context.prototype.indexOf = function (elem) {
        for (var i = 0, a = this.elems, l = a.length; i < l; i++)
            if (elem.equals(a[i]))
                return i;
        return -1;
    };
    Context.prototype.contains = function (elem) {
        return this.indexOf(elem) >= 0;
    };
    Context.prototype.indexOfExistential = function (id) {
        for (var i = 0, a = this.elems, l = a.length; i < l; i++) {
            var c = a[i];
            if ((c instanceof CExists && c.id.equals(id))
                || (c instanceof CExistsSolved && c.id.equals(id)))
                return i;
        }
        return -1;
    };
    Context.prototype.containsExistential = function (id) {
        return this.indexOfExistential(id) >= 0;
    };
    Context.prototype.indexOfVar = function (name) {
        for (var i = 0, a = this.elems, l = a.length; i < l; i++) {
            var c = a[i];
            if (c instanceof CVar && c.name === name)
                return i;
        }
        return -1;
    };
    Context.prototype.containsVar = function (name) {
        return this.indexOfVar(name) >= 0;
    };
    Context.prototype.getSolved = function (id) {
        var i = this.indexOfExistential(id);
        if (i < 0)
            return null;
        var e = this.elems[i];
        return e instanceof CExistsSolved ? e.type : null;
    };
    Context.prototype.getType = function (id) {
        var i = this.indexOfVar(id);
        if (i < 0)
            return null;
        var e = this.elems[i];
        return e instanceof CVar ? e.type : null;
    };
    Context.prototype.isComplete = function () {
        for (var i = 0, a = this.elems, l = a.length; i < l; i++)
            if (!a[i].isComplete())
                return false;
        return true;
    };
    Context.prototype.isWellformed = function () {
        var l = this.elems.length;
        if (l === 0)
            return true;
        var init = this.init();
        return init.isWellformed() && this.elems[l - 1].isWellformed(init);
    };
    Context.prototype.init = function () {
        return new Context(this.elems.slice(0, -1));
    };
    Context.prototype.add = function () {
        var elem = [];
        for (var _i = 0; _i < arguments.length; _i++) {
            elem[_i] = arguments[_i];
        }
        return new Context(this.elems.concat(elem));
    };
    Context.prototype.dropFrom = function (e) {
        var i = this.indexOf(e);
        if (i < 0)
            return this;
        return new Context(this.elems.slice(0, i));
    };
    Context.prototype.split = function (e) {
        var i = this.indexOf(e);
        if (i < 0)
            return [this, Context.empty()];
        return [
            new Context(this.elems.slice(0, i)),
            new Context(this.elems.slice(i + 1)),
        ];
    };
    Context.prototype.isOrdered = function (id1, id2) {
        return this.dropFrom(exports.cexists(id2)).containsExistential(id1);
    };
    Context.prototype.insertAt = function (elem, elems) {
        var _a = this.split(elem), left = _a[0], right = _a[1];
        return new Context(left.elems.concat(elems).concat(right.elems));
    };
    return Context;
}());
exports.Context = Context;
exports.context = function (elems) { return new Context(elems); };
