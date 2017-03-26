var T = require('./types');

var EVar = 'EVar';
var evar = name => ({
  tag: EVar,
  name,
});

var EUnit = 'EUnit';
var eunit = { tag: EUnit };

var EAbs = 'EAbs';
var eabs = (arg, body) => ({
  tag: EAbs,
  arg,
  body,
});
var eabss = function() {
  var l = arguments.length;
  if(l < 2) serr('abs needs at least 2 arguments');
  var c = eabs(arguments[l - 2], arguments[l - 1]);
  for(var i = l - 3; i >= 0; i--) c = eabs(arguments[i], c);
  return c;
};

var EApp = 'EApp';
var eapp = (left, right) => ({
  tag: EApp,
  left,
  right,
});
var eapps = function() {
  var l = arguments.length;
  if(l === 1) return arguments[0];
  if(l < 2) serr('app needs at least one argument');
  var c = eapp(arguments[0], arguments[1]);
  for(var i = 2; i < l; i++) c = eapp(c, arguments[i]);
  return c;
};

var EAnno = 'EAnno';
var eanno = (expr, type) => ({
  tag: EAnno,
  expr,
  type,
});

var EIf = 'EIf';
var eif = (cond, bodyTrue, bodyFalse) => ({
  tag: EIf,
  cond,
  bodyTrue,
  bodyFalse,
});

var EFix = 'Fix';
var efix = { tag: EFix };

var str = e => {
  if(e.tag === EVar) return e.name;
  if(e.tag === EUnit) return '()';
  if(e.tag === EAbs) return '(\\' + e.arg + ' -> ' + str(e.body) + ')';
  if(e.tag === EApp)
    return '(' + str(e.left) + ' ' + str(e.right) + ')';
  if(e.tag === EAnno)
    return '(' + str(e.expr) + ' : ' + T.str(e.type) + ')';
  if(e.tag === EIf)
    return '(if ' + str(e.cond) + ' then ' + str(e.bodyTrue) +
      ' else ' + str(e.bodyFalse) + ')';
  if(e.tag === EFix) return 'fix';
  throw new Error('Invalid expr in exprStr: ' + e);
};

var subst = (e1, x, e2) => {
  if(e2.tag === EVar) return e2.name === x? e1: e2;
  if(e2.tag === EUnit) return e2;
  if(e2.tag === EFix) return e2;
  if(e2.tag === EAbs)
    return e2.arg === x? e2: eabs(e2.arg, subst(e1, x, e2.body));
  if(e2.tag === EApp)
    return eapp(subst(e1, x, e2.left), subst(e1, x, e2.right));
  if(e2.tag === EAnno)
    return eanno(subst(e1, x, e2.expr), e2.type);
  if(e2.tag === EIf)
    return eif(
      subst(e1, x, e2.cond),
      subst(e1, x, e2.bodyTrue),
      subst(e1, x, e2.bodyFalse)
    );
  throw new Error('Cannot subst over ' + e2);
};

module.exports = {
  EVar,
  evar,

  EUnit,
  eunit,

  EAbs,
  eabs,
  eabss,

  EApp,
  eapp,
  eapps,

  EAnno,
  eanno,

  EIf,
  eif,

  EFix,
  efix,

  str,
  subst,
};
