"use strict";
exports.__esModule = true;
var Map_1 = require("./Map");
var Set = (function () {
    function Set(map) {
        this.map = map;
    }
    Set.from = function (args) {
        return new Set(Map_1["default"].from(args.map(function (x) { return [x, x]; })));
    };
    Set.of = function () {
        var args = [];
        for (var _i = 0; _i < arguments.length; _i++) {
            args[_i] = arguments[_i];
        }
        return Set.from(args);
    };
    Set.empty = function () { return Set.of(); };
    Set.prototype.keys = function () { return this.map.keys(); };
    Set.prototype.vals = function () { return this.map.vals(); };
    Set.prototype.toString = function () { return "{" + this.keys().join(', ') + "}"; };
    Set.prototype.contains = function (v) { return !!this.map.contains(v); };
    Set.prototype.union = function (other) {
        return new Set(this.map.union(other.map));
    };
    Set.prototype.without = function (other) {
        return new Set(this.map.removeKeySet(other));
    };
    Set.prototype.remove = function (k) {
        return new Set(this.map.removeKey(k));
    };
    return Set;
}());
exports["default"] = Set;
