var E = require('./exprs');
var T = require('./types');
var K = require('./kinds');
var C = require('./context');

var infer = require('./typechecker').infer;

var Bool = T.tcon('Bool');
var Int = T.tcon('Int');
var List = T.tcon('List', K.star2);
var Pair = T.tcon('Pair', K.star3);

var cvar = C.cvar;
var fun = T.tfuns;
var tapp = T.tapp;
var tapps = T.tapps;
var tforall = T.tforall;
var tforalls = T.tforalls;
var tvar = T.tvar;
var env = [
  cvar('True', Bool),
  cvar('False', Bool),
  cvar('inc', fun(Int, Int)),
  cvar('one', Int),
  cvar('singleton', tforall('t', fun(tvar('t'), tapp(List, tvar('t'))))),
  cvar('map', tforalls(['a', 'b'],
    fun(
      fun(tvar('a'), tvar('b')),
      tapp(List, tvar('a')),
      tapp(List, tvar('b'))
    ))),
  cvar('pair', tforalls(['a', 'b'],
    fun(
      tvar('a'),
      tvar('b'),
      tapps(Pair, tvar('a'), tvar('b'))
    ))),
];

var test = e => {
  console.log(E.str(e));
  try {
    var t = infer(e, env);
    console.log(T.str(t) + ' : ' + K.str(t.kind));
  } catch(e) {
    console.log('' + e);
  }
  console.log();
};

var eanno = E.eanno;
var abs = E.eabss;
var evar = E.evar;
var app = E.eapps;
var eunit = E.eunit;

var eid = eanno(abs('x', evar('x')), tforall('t', fun(tvar('t'), tvar('t'))));
[
  eunit,

  app(abs('x', evar('x')), eunit),

  abs('x', evar('x')),

  // (\x -> x) : forall t . t -> t
  eid,

  // idunit
  app(abs('id', app(evar('id'), eunit)), eid),

  // idid
  eanno(app(eid, eid), tforall('t', fun(tvar('t'), tvar('t')))),

  // (\id -> id id ()) ((\x -> x) : forall t . t -> t)
  abs('id',
    app(
      eanno(
        evar('id'),
        tforall('t', fun(tvar('t'), tvar('t')))
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

  evar('pair'),
  app(evar('pair'), evar('one')),
  app(evar('pair'), evar('one'), evar('True')),

  app(eanno(
    abs('id',
      app(evar('pair'),
        app(evar('id'), evar('one')), app(evar('id'), evar('True')))),
        fun(tforall('t', fun(tvar('t'), tvar('t'))), tapps(Pair, Int, Bool))
      ), eid),
].forEach(test);
