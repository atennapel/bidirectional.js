var T = require('./types');

var CForall = 'CForall';
var cforall = name => ({
  tag: CForall,
  name,
});

var CVar = 'CVar';
var cvar = (name, type) => ({
  tag: CVar,
  name,
  type,
});

var CExists = 'CExists';
var cexists = name => ({
  tag: CExists,
  name,
});

var CExistsSolved = 'CExistsSolved';
var cexistssolved = (name, type) => ({
  tag: CExistsSolved,
  name,
  type,
});

var CMarker = 'CMarker';
var cmarker = name => ({
  tag: CMarker,
  name,
});

var elemStr = e => {
  if(e.tag === CForall) return e.name;
  if(e.tag === CVar) return e.name + ' : ' + T.str(e.type);
  if(e.tag === CExists) return e.name + '^';
  if(e.tag === CExistsSolved) return e.name + ' = ' + T.str(e.type);
  if(e.tag === CMarker) return '|>' + e.name + '^';
  throw new Error('Invalid elem in elemStr: ' + e);
};

var contextStr = c => '[' + c.map(elemStr).reverse().join(', ') + ']';

var elemEq = (a, b) => {
  if(a.tag === CForall) return b.tag === CForall && a.name === b.name;
  if(a.tag === CVar)
    return b.tag === CVar && a.name === b.name && T.eq(a.type, b.type);
  if(a.tag === CExists) return b.tag === CExists && a.name === b.name;
  if(a.tag === CExistsSolved)
    return b.tag === CExistsSolved &&
      a.name === b.name && T.eq(a.type, b.type);
  if(a.tag === CMarker) return b.tag === CMarker && a.name === b.name;
  throw new Error('Invalid elem in elemEq: ' + a);
};

var isComplete = c => {
  for(var i = 0, l = c.length; i < l; i++)
    if(c[i].tag === CExists) return false;
  return true;
};

var snoc = (c, e) => [e].concat(c);
var empty = [];
var append = (a, b) => b.concat(a);
var context = c => c.slice(0).reverse();
var appendElems = (c, es) => append(c, context(es));
var dropMarker = (m, g) => {
  for(var i = 0, l = g.length; i < l; i++)
    if(elemEq(g[i], m)) return g.slice(i + 1);
  return [];
};
var breakMarker = (m, g) => {
  for(var i = 0, l = g.length; i < l; i++)
    if(elemEq(g[i], m)) return [g.slice(i + 1), g.slice(0, i)];
  return [[], g];
};
var insertAt = (gamma, c, theta) => {
  var broken = breakMarker(c, gamma);
  return append(broken[0], append(theta, broken[1]));
};

var existentials = c => {
  var r = [];
  for(var i = 0, l = c.length; i < l; i++)
    if(c[i].tag === CExists || c[i].tag === CExistsSolved) r.push(c[i].name);
  return r;
};

var unsolved = c => {
  var r = [];
  for(var i = 0, l = c.length; i < l; i++)
    if(c[i].tag === CExists) r.push(c[i].name);
  return r;
};

var vars = c => {
  var r = [];
  for(var i = 0, l = c.length; i < l; i++)
    if(c[i].tag === CVar) r.push(c[i].name);
  return r;
};

var foralls = c => {
  var r = [];
  for(var i = 0, l = c.length; i < l; i++)
    if(c[i].tag === CForall) r.push(c[i].name);
  return r;
};

var markers = c => {
  var r = [];
  for(var i = 0, l = c.length; i < l; i++)
    if(c[i].tag === CMarker) r.push(c[i].name);
  return r;
};

module.exports = {
  CForall,
  cforall,

  CVar,
  cvar,

  CExists,
  cexists,

  CExistsSolved,
  cexistssolved,

  CMarker,
  cmarker,

  elemStr,
  contextStr,
  elemEq,

  isComplete,

  snoc,
  empty,
  append,
  context,
  appendElems,
  dropMarker,
  breakMarker,
  insertAt,

  existentials,
  unsolved,
  vars,
  foralls,
  markers,
};
