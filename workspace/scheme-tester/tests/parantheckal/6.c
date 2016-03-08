#include <setjmp.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "6.h"

void *expr_const(void *n) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _const_exp;
  _data->u._const._n = n;
  return (void *)_data;
}

void *expr_var(void *v) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _var_exp;
  _data->u._var._v = v;
  return (void *)_data;
}

void *expr_if(void *test, void *conseq, void *alt) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _if_exp;
  _data->u._if._test = test;
  _data->u._if._conseq = conseq;
  _data->u._if._alt = alt;
  return (void *)_data;
}

void *expr_mult(void *randr1, void *randr2) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _mult_exp;
  _data->u._mult._randr1 = randr1;
  _data->u._mult._randr2 = randr2;
  return (void *)_data;
}

void *expr_subr1(void *rand) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _subr1_exp;
  _data->u._subr1._rand = rand;
  return (void *)_data;
}

void *expr_zero(void *rand) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _zero_exp;
  _data->u._zero._rand = rand;
  return (void *)_data;
}

void *expr_letcc(void *body) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _letcc_exp;
  _data->u._letcc._body = body;
  return (void *)_data;
}

void *expr_throw(void *vexp, void *kexp) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _throw_exp;
  _data->u._throw._vexp = vexp;
  _data->u._throw._kexp = kexp;
  return (void *)_data;
}

void *expr_let(void *vexp, void *body) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _let_exp;
  _data->u._let._vexp = vexp;
  _data->u._let._body = body;
  return (void *)_data;
}

void *expr_lambda(void *body) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _lambda_exp;
  _data->u._lambda._body = body;
  return (void *)_data;
}

void *expr_app(void *rator, void *rand) {
exp* _data = (exp*)malloc(sizeof(exp));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _app_exp;
  _data->u._app._rator = rator;
  _data->u._app._rand = rand;
  return (void *)_data;
}

void *envrr_empty() {
envr* _data = (envr*)malloc(sizeof(envr));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _empty_envr;
  return (void *)_data;
}

void *envrr_extend(void *arg, void *env) {
envr* _data = (envr*)malloc(sizeof(envr));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _extend_envr;
  _data->u._extend._arg = arg;
  _data->u._extend._env = env;
  return (void *)_data;
}

void *closr_closure(void *code, void *env) {
clos* _data = (clos*)malloc(sizeof(clos));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _closure_clos;
  _data->u._closure._code = code;
  _data->u._closure._env = env;
  return (void *)_data;
}

void *kontr_emptyr__m__k(void *dismount) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _emptyr__m__k_kont;
  _data->u._emptyr__m__k._dismount = dismount;
  return (void *)_data;
}

void *kontr_multr__m__kr1(void *randr2, void *env, void *k) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _multr__m__kr1_kont;
  _data->u._multr__m__kr1._randr2 = randr2;
  _data->u._multr__m__kr1._env = env;
  _data->u._multr__m__kr1._k = k;
  return (void *)_data;
}

void *kontr_multr__m__kr2(void *w, void *k) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _multr__m__kr2_kont;
  _data->u._multr__m__kr2._w = w;
  _data->u._multr__m__kr2._k = k;
  return (void *)_data;
}

void *kontr_subr1r__m__k(void *k) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _subr1r__m__k_kont;
  _data->u._subr1r__m__k._k = k;
  return (void *)_data;
}

void *kontr_zeror__q__r__m__k(void *k) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _zeror__q__r__m__k_kont;
  _data->u._zeror__q__r__m__k._k = k;
  return (void *)_data;
}

void *kontr_ifr__m__k(void *conseq, void *alt, void *env, void *k) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _ifr__m__k_kont;
  _data->u._ifr__m__k._conseq = conseq;
  _data->u._ifr__m__k._alt = alt;
  _data->u._ifr__m__k._env = env;
  _data->u._ifr__m__k._k = k;
  return (void *)_data;
}

void *kontr_cr__m__k(void *vexp, void *env) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _cr__m__k_kont;
  _data->u._cr__m__k._vexp = vexp;
  _data->u._cr__m__k._env = env;
  return (void *)_data;
}

void *kontr_letr__m__k(void *body, void *env, void *k) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _letr__m__k_kont;
  _data->u._letr__m__k._body = body;
  _data->u._letr__m__k._env = env;
  _data->u._letr__m__k._k = k;
  return (void *)_data;
}

void *kontr_procr__m__k(void *rand, void *env, void *k) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _procr__m__k_kont;
  _data->u._procr__m__k._rand = rand;
  _data->u._procr__m__k._env = env;
  _data->u._procr__m__k._k = k;
  return (void *)_data;
}

void *kontr_argr__m__k(void *proc, void *k) {
kont* _data = (kont*)malloc(sizeof(kont));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _argr__m__k_kont;
  _data->u._argr__m__k._proc = proc;
  _data->u._argr__m__k._k = k;
  return (void *)_data;
}

void valuer__m__of()
{
exp* _c = (exp*)r__t__exprr__t__;
switch (_c->tag) {
case _const_exp: {
void *n = _c->u._const._n;
r__t__vr__t__ = (void *)n;
r__t__pcr__t__ = &applyr__m__k;
break; }
case _var_exp: {
void *v = _c->u._var._v;
r__t__numr__t__ = (void *)v;
r__t__pcr__t__ = &applyr__m__env;
break; }
case _if_exp: {
void *test = _c->u._if._test;
void *conseq = _c->u._if._conseq;
void *alt = _c->u._if._alt;
r__t__kr__t__ = (void *)kontr_ifr__m__k(conseq,alt,r__t__envr__t__,r__t__kr__t__);
r__t__exprr__t__ = (void *)test;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _mult_exp: {
void *randr1 = _c->u._mult._randr1;
void *randr2 = _c->u._mult._randr2;
r__t__kr__t__ = (void *)kontr_multr__m__kr1(randr2,r__t__envr__t__,r__t__kr__t__);
r__t__exprr__t__ = (void *)randr1;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _subr1_exp: {
void *rand = _c->u._subr1._rand;
r__t__kr__t__ = (void *)kontr_subr1r__m__k(r__t__kr__t__);
r__t__exprr__t__ = (void *)rand;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _zero_exp: {
void *rand = _c->u._zero._rand;
r__t__kr__t__ = (void *)kontr_zeror__q__r__m__k(r__t__kr__t__);
r__t__exprr__t__ = (void *)rand;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _letcc_exp: {
void *body = _c->u._letcc._body;
r__t__envr__t__ = (void *)envrr_extend(r__t__kr__t__,r__t__envr__t__);
r__t__exprr__t__ = (void *)body;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _throw_exp: {
void *vexp = _c->u._throw._vexp;
void *kexp = _c->u._throw._kexp;
r__t__kr__t__ = (void *)kontr_cr__m__k(vexp,r__t__envr__t__);
r__t__exprr__t__ = (void *)kexp;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _let_exp: {
void *vexp = _c->u._let._vexp;
void *body = _c->u._let._body;
r__t__kr__t__ = (void *)kontr_letr__m__k(body,r__t__envr__t__,r__t__kr__t__);
r__t__exprr__t__ = (void *)vexp;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _lambda_exp: {
void *body = _c->u._lambda._body;
r__t__vr__t__ = (void *)closr_closure(body,r__t__envr__t__);
r__t__pcr__t__ = &applyr__m__k;
break; }
case _app_exp: {
void *rator = _c->u._app._rator;
void *rand = _c->u._app._rand;
r__t__kr__t__ = (void *)kontr_procr__m__k(rand,r__t__envr__t__,r__t__kr__t__);
r__t__exprr__t__ = (void *)rator;
r__t__pcr__t__ = &valuer__m__of;
break; }
}
}

void applyr__m__env()
{
envr* _c = (envr*)r__t__envr__t__;
switch (_c->tag) {
case _empty_envr: {
fprintf(stderr, "unbound variable");
 exit(1);
break; }
case _extend_envr: {
void *arg = _c->u._extend._arg;
void *env = _c->u._extend._env;
if((r__t__numr__t__ == 0)) {
  r__t__vr__t__ = (void *)arg;
r__t__pcr__t__ = &applyr__m__k;

} else {
  r__t__numr__t__ = (void *)(void *)((int)r__t__numr__t__ - 1);
r__t__envr__t__ = (void *)env;
r__t__pcr__t__ = &applyr__m__env;

}
break; }
}
}

void applyr__m__proc()
{
clos* _c = (clos*)r__t__cr__t__;
switch (_c->tag) {
case _closure_clos: {
void *code = _c->u._closure._code;
void *env = _c->u._closure._env;
r__t__exprr__t__ = (void *)code;
r__t__envr__t__ = (void *)envrr_extend(r__t__ar__t__,env);
r__t__pcr__t__ = &valuer__m__of;
break; }
}
}

void applyr__m__k()
{
kont* _c = (kont*)r__t__kr__t__;
switch (_c->tag) {
case _emptyr__m__k_kont: {
void *dismount = _c->u._emptyr__m__k._dismount;
_trstr *trstr = (_trstr *)dismount;
longjmp(*trstr->jmpbuf, 1);
break; }
case _multr__m__kr1_kont: {
void *randr2 = _c->u._multr__m__kr1._randr2;
void *env = _c->u._multr__m__kr1._env;
void *k = _c->u._multr__m__kr1._k;
r__t__kr__t__ = (void *)kontr_multr__m__kr2(r__t__vr__t__,k);
r__t__exprr__t__ = (void *)randr2;
r__t__envr__t__ = (void *)env;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _multr__m__kr2_kont: {
void *w = _c->u._multr__m__kr2._w;
void *k = _c->u._multr__m__kr2._k;
r__t__kr__t__ = (void *)k;
r__t__vr__t__ = (void *)(void *)((int)w * (int)r__t__vr__t__);
r__t__pcr__t__ = &applyr__m__k;
break; }
case _subr1r__m__k_kont: {
void *k = _c->u._subr1r__m__k._k;
r__t__kr__t__ = (void *)k;
r__t__vr__t__ = (void *)(void *)((int)r__t__vr__t__ - 1);
r__t__pcr__t__ = &applyr__m__k;
break; }
case _zeror__q__r__m__k_kont: {
void *k = _c->u._zeror__q__r__m__k._k;
r__t__kr__t__ = (void *)k;
r__t__vr__t__ = (void *)(r__t__vr__t__ == 0);
r__t__pcr__t__ = &applyr__m__k;
break; }
case _ifr__m__k_kont: {
void *conseq = _c->u._ifr__m__k._conseq;
void *alt = _c->u._ifr__m__k._alt;
void *env = _c->u._ifr__m__k._env;
void *k = _c->u._ifr__m__k._k;
if(r__t__vr__t__) {
  r__t__kr__t__ = (void *)k;
r__t__exprr__t__ = (void *)conseq;
r__t__envr__t__ = (void *)env;
r__t__pcr__t__ = &valuer__m__of;

} else {
  r__t__kr__t__ = (void *)k;
r__t__exprr__t__ = (void *)alt;
r__t__envr__t__ = (void *)env;
r__t__pcr__t__ = &valuer__m__of;

}
break; }
case _cr__m__k_kont: {
void *vexp = _c->u._cr__m__k._vexp;
void *env = _c->u._cr__m__k._env;
r__t__kr__t__ = (void *)r__t__vr__t__;
r__t__exprr__t__ = (void *)vexp;
r__t__envr__t__ = (void *)env;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _letr__m__k_kont: {
void *body = _c->u._letr__m__k._body;
void *env = _c->u._letr__m__k._env;
void *k = _c->u._letr__m__k._k;
r__t__kr__t__ = (void *)k;
r__t__exprr__t__ = (void *)body;
r__t__envr__t__ = (void *)envrr_extend(r__t__vr__t__,env);
r__t__pcr__t__ = &valuer__m__of;
break; }
case _procr__m__k_kont: {
void *rand = _c->u._procr__m__k._rand;
void *env = _c->u._procr__m__k._env;
void *k = _c->u._procr__m__k._k;
r__t__kr__t__ = (void *)kontr_argr__m__k(r__t__vr__t__,k);
r__t__exprr__t__ = (void *)rand;
r__t__envr__t__ = (void *)env;
r__t__pcr__t__ = &valuer__m__of;
break; }
case _argr__m__k_kont: {
void *proc = _c->u._argr__m__k._proc;
void *k = _c->u._argr__m__k._k;
r__t__kr__t__ = (void *)k;
r__t__cr__t__ = (void *)proc;
r__t__ar__t__ = (void *)r__t__vr__t__;
r__t__pcr__t__ = &applyr__m__proc;
break; }
}
}

int main()
{
r__t__exprr__t__ = (void *)expr_app(expr_lambda(expr_app(expr_app(expr_var((void *)0),expr_var((void *)0)),expr_const((void *)5))),expr_lambda(expr_lambda(expr_if(expr_zero(expr_var((void *)0)),expr_const((void *)1),expr_mult(expr_var((void *)0),expr_app(expr_app(expr_var((void *)1),expr_var((void *)1)),expr_subr1(expr_var((void *)0))))))));
r__t__envr__t__ = (void *)envrr_empty();
r__t__pcr__t__ = &valuer__m__of;
mount_tram();
printf("%d\n", (int)r__t__vr__t__);r__t__exprr__t__ = (void *)expr_mult(expr_const((void *)2),expr_letcc(expr_mult(expr_const((void *)5),expr_throw(expr_mult(expr_const((void *)2),expr_const((void *)6)),expr_var((void *)0)))));
r__t__envr__t__ = (void *)envrr_empty();
r__t__pcr__t__ = &valuer__m__of;
mount_tram();
printf("%d\n", (int)r__t__vr__t__);r__t__exprr__t__ = (void *)expr_let(expr_lambda(expr_lambda(expr_if(expr_zero(expr_var((void *)0)),expr_const((void *)1),expr_mult(expr_var((void *)0),expr_app(expr_app(expr_var((void *)1),expr_var((void *)1)),expr_subr1(expr_var((void *)0))))))),expr_app(expr_app(expr_var((void *)0),expr_var((void *)0)),expr_const((void *)5)));
r__t__envr__t__ = (void *)envrr_empty();
r__t__pcr__t__ = &valuer__m__of;
mount_tram();
printf("%d\n", (int)r__t__vr__t__);}

int mount_tram ()
{
srand (time (NULL));
jmp_buf jb;
_trstr trstr;
void *dismount;
int _status = setjmp(jb);
trstr.jmpbuf = &jb;
dismount = &trstr;
if(!_status) {
r__t__kr__t__= (void *)kontr_emptyr__m__k(dismount);
for(;;) {
r__t__pcr__t__();
}
}
return 0;
}
