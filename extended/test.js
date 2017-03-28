var E = require('./exprs');
var T = require('./types');
var K = require('./kinds');
var C = require('./context');

var infer = require('./typechecker').infer;

var Bool = T.tbool;
var Int = T.tcon('Int');
var List = T.tcon('List', K.ktype2);
var Pair = T.tcon('Pair', K.ktype3);

var cvar = C.cvar;
var fun = T.tfuns;
var tapp = T.tapp;
var tapps = T.tapps;
var tforall = T.tforall;
var tforalls = T.tforalls;
var tvar = T.tvar;
var a = tvar('a');
var b = tvar('b');
var t = tvar('t');
var f = tvar('f', K.ktype2);
var env = [
  cvar('True', Bool),
  cvar('False', Bool),
  cvar('inc', fun(Int, Int)),
  cvar('one', Int),
  cvar('singleton', tforall(t, fun(t, tapp(List, t)))),
  cvar('map', tforalls([f, a, b],
    fun(
      fun(a, b),
      tapp(f, a),
      tapp(f, b)
    ))),
  cvar('pair', tforalls([a, b], fun(a, b, tapps(Pair, a, b)))),
  cvar('Pair', Pair),
];

var test = e => {
  console.log(E.str(e));
  try {
    var t = infer(e, env);
    console.log(T.str(t) + ' : ' + K.str(t.kind));
  } catch(e) {
    console.log('' + e.stack);
  }
  console.log();
};

var eanno = E.eanno;
var abs = E.eabss;
var evar = E.evar;
var app = E.eapps;
var eunit = E.eunit;
var eif = E.eif;
var fix = E.efix;

var eid = eanno(abs('x', evar('x')), tforall(t, fun(t, t)));
[
  eunit,

  app(abs('x', evar('x')), eunit),

  abs('x', evar('x')),

  // (\x -> x) : forall t . t -> t
  eid,

  // idunit
  app(abs('id', app(evar('id'), eunit)), eid),

  // idid
  eanno(app(eid, eid), tforall(t, fun(t, t))),

  // (\id -> id id ()) ((\x -> x) : forall t . t -> t)
  abs('id',
    app(
      eanno(
        evar('id'),
        tforall(t, fun(t, t))
      ),
      evar('id'),
      eunit,
      eid
    )
  ),

  app(evar('inc'), eunit),
  app(evar('inc'), evar('one')),
  abs('x', 'y', evar('x')),
  evar('singleton'),
  app(evar('singleton'), evar('one')),
  app(evar('singleton'), eid),

  evar('map'),
  app(evar('map'), evar('inc')),
  app(evar('map'), evar('inc'), app(evar('singleton'), evar('one'))),
  app(evar('map'), evar('inc'), app(evar('pair'), evar('True'), evar('one'))),

  evar('pair'),
  app(evar('pair'), evar('one')),
  app(evar('pair'), evar('one'), evar('True')),

  app(eanno(
    abs('id',
      app(evar('pair'),
        app(evar('id'), evar('one')), app(evar('id'), evar('True')))),
        fun(tforall(t, fun(t, t)), tapps(Pair, Int, Bool))
      ), eid),

  eif(evar('True'), evar('False'), evar('True')),
  eif(evar('one'), evar('False'), evar('True')),
  eif(evar('True'), evar('one'), evar('True')),
  eif(evar('True'), evar('False'), evar('one')),
  eif(evar('True'), evar('one'), evar('one')),

  abs('x', eif(evar('x'), evar('one'), evar('one'))),
  abs('x', 'y', eif(evar('x'), evar('y'), evar('one'))),
  abs('x', 'y', eif(evar('x'), evar('y'), evar('y'))),
  abs('x', 'y', eif(evar('x'), evar('y'), evar('x'))),

  fix,
  app(fix, abs('f', 'x',
    eif(evar('True'),
      app(evar('inc'), evar('x')),
      app(evar('f'), evar('x'))))),
  app(fix, abs('f', 'x',
    eif(evar('True'),
      evar('x'),
      app(evar('f'), evar('x'))))),

  evar('Pair'),
].forEach(test);
