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
var Expr = (function () {
    function Expr() {
    }
    return Expr;
}());
exports.Expr = Expr;
var EVar = (function (_super) {
    __extends(EVar, _super);
    function EVar(name) {
        var _this = _super.call(this) || this;
        _this.name = name;
        return _this;
    }
    EVar.prototype.toString = function () {
        return this.name;
    };
    EVar.prototype.subst = function (id, expr) {
        return this.name === id ? expr : this;
    };
    return EVar;
}(Expr));
exports.EVar = EVar;
exports.evar = function (name) { return new EVar(name); };
var EUnit = (function (_super) {
    __extends(EUnit, _super);
    function EUnit() {
        return _super.call(this) || this;
    }
    EUnit.prototype.toString = function () {
        return '()';
    };
    EUnit.prototype.subst = function (id, expr) {
        return this;
    };
    return EUnit;
}(Expr));
exports.EUnit = EUnit;
exports.eunit = new EUnit();
var ELam = (function (_super) {
    __extends(ELam, _super);
    function ELam(arg, body) {
        var _this = _super.call(this) || this;
        _this.arg = arg;
        _this.body = body;
        return _this;
    }
    ELam.prototype.toString = function () {
        return "(\\" + this.arg + " -> " + this.body + ")";
    };
    ELam.prototype.subst = function (id, expr) {
        return this.arg === id ? this : new ELam(this.arg, this.body.subst(id, expr));
    };
    return ELam;
}(Expr));
exports.ELam = ELam;
exports.elam = function (arg, body) { return new ELam(arg, body); };
exports.elams = function (args, body) {
    if (args.length < 1)
        throw new Error('Not enough arguments for elams');
    return args.reduceRight(function (x, y) { return exports.elam(y, x); }, body);
};
var EApp = (function (_super) {
    __extends(EApp, _super);
    function EApp(left, right) {
        var _this = _super.call(this) || this;
        _this.left = left;
        _this.right = right;
        return _this;
    }
    EApp.prototype.toString = function () {
        return "(" + this.left + " " + this.right + ")";
    };
    EApp.prototype.subst = function (id, expr) {
        return new EApp(this.left.subst(id, expr), this.right.subst(id, expr));
    };
    return EApp;
}(Expr));
exports.EApp = EApp;
exports.eapp = function (left, right) { return new EApp(left, right); };
exports.eapps = function (es) {
    if (es.length < 2)
        throw new Error('Not enough arguments for elams');
    return es.reduce(exports.eapp);
};
var EAnno = (function (_super) {
    __extends(EAnno, _super);
    function EAnno(expr, type) {
        var _this = _super.call(this) || this;
        _this.expr = expr;
        _this.type = type;
        return _this;
    }
    EAnno.prototype.toString = function () {
        return "(" + this.expr + " : " + this.type + ")";
    };
    EAnno.prototype.subst = function (id, expr) {
        return new EAnno(this.expr.subst(id, expr), this.type);
    };
    return EAnno;
}(Expr));
exports.EAnno = EAnno;
exports.eanno = function (expr, type) { return new EAnno(expr, type); };
