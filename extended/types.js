var K = require('./kinds');

var TCon = 'TCon';
var tcon = (name, kind) => ({
  tag: TCon,
  name,
  kind: kind || K.star,
});

var TVar = 'TVar';
var tvar = (name, kind) => ({
  tag: TVar,
  name,
  kind: kind || K.star,
});

var TExists = 'TExists';
var texists = (name, kind) => ({
  tag: TExists,
  name,
  kind: kind || K.star,
});

var TForall = 'TForall';
var tforall = (arg, type) => ({
  tag: TForall,
  arg,
  type,
  kind: type.kind,
});
var tforalls = (args, type) =>
  args.reduceRight((t, arg) => tforall(arg, t), type);

var TFun = 'TFun';
var tfun = (left, right) => {
  if(!K.eq(left.kind, K.star))
    throw new Error(str(left) + ' has invalid kind (' + K.star(left.kind)
      + ') in (' + str(left) + ' -> ' + str(right) + ')');
  if(!K.eq(right.kind, K.star))
    throw new Error(str(right) + ' has invalid kind (' + K.star(right.kind)
      + ') in (' + str(left) + ' -> ' + str(right) + ')');
  return {
    tag: TFun,
    left,
    right,
    kind: K.star,
  };
};
var tfuns = function() {
  var l = arguments.length;
  if(l < 2) T.terr('fun needs at least 2 arguments');
  var c = tfun(arguments[l - 2], arguments[l - 1]);
  for(var i = l - 3; i >= 0; i--) c = tfun(arguments[i], c);
  return c;
};

var TApp = 'TApp';
var tapp = (left, right) => {
  if(left.kind.tag !== K.KFun)
    throw new Error('Cannot type apply (' + str(left) + ' ' + str(right) +
      '): left side has invalid kind ' + K.str(left.kind));
  if(!K.eq(left.kind.left, right.kind))
    throw new Error('Cannot type apply (' + str(left) + ' ' + str(right) +
      '): right side has invalid kind ' + K.str(right.kind));
  return {
    tag: TApp,
    left,
    right,
    kind: left.kind.right,
  };
};
var tapps = function() {
  var l = arguments.length;
  if(l < 2) terr('tapp needs at least two arguments');
  var c = tapp(arguments[0], arguments[1]);
  for(var i = 2; i < l; i++) c = tapp(c, arguments[i]);
  return c;
};

var tunit = tcon('Unit', K.star);

var str = t => {
  if(t.tag === TCon) return t.name;
  if(t.tag === TVar) return t.name;
  if(t.tag === TExists) return t.name + '^';
  if(t.tag === TForall)
    return '(forall ' + t.arg + ' . ' + str(t.type) + ')';
  if(t.tag === TFun)
    return '(' + str(t.left) + ' -> ' + str(t.right) + ')';
  if(t.tag === TApp)
    return '(' + str(t.left) + ' ' + str(t.right) + ')';
  throw new Error('Invalid type in typeStr: ' + t);
};

var eq = (a, b) => {
  if(a.tag === TCon) return b.tag === TCon && a.name === b.name;
  if(a.tag === TVar) return b.tag === TVar && a.name === b.name;
  if(a.tag === TExists) return b.tag === TExists && a.name === b.name;
  if(a.tag === TForall)
    return b.tag === TForall && a.arg === b.arg && eq(a.type, b.type);
  if(a.tag === TFun)
    return b.tag === TFun && eq(a.left, b.left) && eq(a.right, b.right);
  if(a.tag === TApp)
    return b.tag === TApp && eq(a.left, b.left) && eq(a.right, b.right);
  throw new Error('Invalid type in typeEq: ' + a);
};

var isMonotype = t => {
  if(t.tag === TCon) return true;
  if(t.tag === TVar) return true;
  if(t.tag === TForall) return false;
  if(t.tag === TExists) return true;
  if(t.tag === TFun) return isMonotype(t.left) && isMonotype(t.right);
  if(t.tag === TApp) return isMonotype(t.left) && isMonotype(t.right);
  throw new Error('Cannot call isMonotype on ' + t);
};

var freeTVars = t => {
  if(t.tag === TCon) return [];
  if(t.tag === TVar) return [t.name];
  if(t.tag === TForall) return freeTVars(t.type).filter(v => v !== t.arg);
  if(t.tag === TExists) return [t.name];
  if(t.tag === TFun) return freeTVars(t.left).concat(freeTVars(t.right));
  if(t.tag === TApp) return freeTVars(t.left).concat(freeTVars(t.right));
  throw new Error('Cannot freeTVars on ' + t);
};

var subst = (t1, v, t2) => {
  if(t2.tag === TCon) return t2;
  if(t2.tag === TVar) return t2.name === v? t1: t2;
  if(t2.tag === TForall)
    return t2.arg === v? t2: tforall(t2.arg, subst(t1, v, t2.type));
  if(t2.tag === TExists) return t2.name === v? t1: t2;
  if(t2.tag === TFun)
    return tfun(subst(t1, v, t2.left), subst(t1, v, t2.right));
  if(t2.tag === TApp)
    return tapp(subst(t1, v, t2.left), subst(t1, v, t2.right));
  throw new Error('Cannot typeSubst over ' + t2);
};

var substs = (subs, type) =>
  subs.reduceRight((t, sub) => subst(sub[0], sub[1], t), type);

module.exports = {
  TCon,
  tcon,

  TVar,
  tvar,

  TExists,
  texists,

  TForall,
  tforall,
  tforalls,

  TFun,
  tfun,
  tfuns,

  TApp,
  tapp,
  tapps,

  tunit,

  str,
  eq,
  isMonotype,
  freeTVars,
  subst,
  substs,
};
