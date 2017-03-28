var KCon = 'KCon';
var kcon = name => ({
  tag: KCon,
  name,
});

var KFun = 'KFun';
var kfun = (left, right) => ({
  tag: KFun,
  left,
  right,
});
var kfuns = function() {
  var l = arguments.length;
  if(l < 2) T.terr('karrs needs at least 2 arguments');
  var c = kfun(arguments[l - 2], arguments[l - 1]);
  for(var i = l - 3; i >= 0; i--) c = kfun(arguments[i], c);
  return c;
};

var ktype = kcon('Type');
var ktype2 = kfun(ktype, ktype);
var ktype3 = kfuns(ktype, ktype, ktype);

var str = k => {
  if(k.tag === KCon) return k.name;
  if(t.tag === KFun)
    return '(' + str(k.left) + ' -> ' + str(k.right) + ')';
  throw new Error('Invalid kind in kindStr: ' + k);
};

var eq = (a, b) => {
  if(a.tag === KCon) return b.tag === KCon && a.name === b.name;
  if(a.tag === KFun)
    return b.tag === KFun && eq(a.left, b.left) && eq(a.right, b.right);
  throw new Error('Invalid kind in kindEq: ' + a);
};

module.exports = {
  KCon,
  kcon,

  KFun,
  kfun,
  kfuns,

  ktype,
  ktype2,
  ktype3,

  str,
  eq,
};
