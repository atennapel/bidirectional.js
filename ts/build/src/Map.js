"use strict";
exports.__esModule = true;
var utils_1 = require("./utils");
var Map = (function () {
    function Map(map) {
        this.imap = map;
    }
    Map.from = function (pairs) {
        var map = {};
        for (var i = 0, l = pairs.length; i < l; i++)
            map[pairs[i][0].hash] = pairs[i][1];
        return new Map(map);
    };
    Map.of = function () {
        var pairs = [];
        for (var _i = 0; _i < arguments.length; _i++) {
            pairs[_i] = arguments[_i];
        }
        return Map.from(pairs);
    };
    Map.empty = function () { return Map.of(); };
    Map.prototype.keys = function () { return Object.keys(this.imap); };
    Map.prototype.vals = function () {
        var _this = this;
        return this.keys().map(function (k) { return _this.imap[k]; });
    };
    Map.prototype.get = function (key) { return this.imap[key.hash]; };
    Map.prototype.getOr = function (key, def) { return this.imap[key.hash] || def; };
    Map.prototype.contains = function (key) { return !!this.get(key); };
    Map.prototype.toString = function () {
        var _this = this;
        return "{" + this.keys().map(function (k) { return k + ": " + _this.imap[k]; }).join(', ') + "}";
    };
    Map.prototype.map = function (fn) {
        var n = {};
        for (var k in this.imap)
            n[k] = fn(this.imap[k]);
        return new Map(n);
    };
    Map.prototype.union = function (other) {
        var n = {};
        for (var k in this.imap)
            n[k] = this.imap[k];
        for (var k in other.imap)
            n[k] = other.imap[k];
        return new Map(n);
    };
    Map.prototype.removeKeysArray = function (keys) {
        var n = utils_1.clone(this.imap);
        for (var i = 0, l = keys.length; i < l; i++)
            delete n[keys[i].hash];
        return new Map(n);
    };
    Map.prototype.removeKeys = function () {
        var keys = [];
        for (var _i = 0; _i < arguments.length; _i++) {
            keys[_i] = arguments[_i];
        }
        return this.removeKeysArray(keys);
    };
    Map.prototype.removeKey = function (k) {
        return this.removeKeys(k);
    };
    Map.prototype.removeKeySet = function (ks) {
        return this.removeKeysArray(ks.vals());
    };
    return Map;
}());
exports["default"] = Map;
