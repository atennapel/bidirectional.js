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
var Result = (function () {
    function Result() {
    }
    Result.ok = function (t) { return new Ok(t); };
    Result.err = function (e) { return new Err(e); };
    return Result;
}());
exports.Result = Result;
var Ok = (function (_super) {
    __extends(Ok, _super);
    function Ok(val) {
        var _this = _super.call(this) || this;
        _this.val = val;
        return _this;
    }
    Ok.prototype.toString = function () { return 'Ok(' + this.val + ')'; };
    Ok.prototype.map = function (fn) { return new Ok(fn(this.val)); };
    Ok.prototype.then = function (fn) { return fn(this.val); };
    Ok.prototype.onErr = function (fn) { return this; };
    return Ok;
}(Result));
exports.Ok = Ok;
var Err = (function (_super) {
    __extends(Err, _super);
    function Err(val) {
        var _this = _super.call(this) || this;
        _this.val = val;
        return _this;
    }
    Err.prototype.toString = function () { return 'Err(' + this.val + ')'; };
    Err.prototype.map = function (fn) { return this; };
    Err.prototype.then = function (fn) { return this; };
    Err.prototype.onErr = function (fn) { return fn(this.val); };
    return Err;
}(Result));
exports.Err = Err;
