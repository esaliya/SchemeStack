#include <setjmp.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "a9-4.h"

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

void *ktr_emptyr_k(void *dismount) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _emptyr_k_kt;
  _data->u._emptyr_k._dismount = dismount;
  return (void *)_data;
}

void *ktr_ifr_k(void *conseq, void *alt, void *env, void *k) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _ifr_k_kt;
  _data->u._ifr_k._conseq = conseq;
  _data->u._ifr_k._alt = alt;
  _data->u._ifr_k._env = env;
  _data->u._ifr_k._k = k;
  return (void *)_data;
}

void *ktr_mulr1r_k(void *randr2, void *env, void *k) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _mulr1r_k_kt;
  _data->u._mulr1r_k._randr2 = randr2;
  _data->u._mulr1r_k._env = env;
  _data->u._mulr1r_k._k = k;
  return (void *)_data;
}

void *ktr_mulr2r_k(void *w, void *k) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _mulr2r_k_kt;
  _data->u._mulr2r_k._w = w;
  _data->u._mulr2r_k._k = k;
  return (void *)_data;
}

void *ktr_subr_k(void *k) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _subr_k_kt;
  _data->u._subr_k._k = k;
  return (void *)_data;
}

void *ktr_zeror_k(void *k) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _zeror_k_kt;
  _data->u._zeror_k._k = k;
  return (void *)_data;
}

void *ktr_throwr_k(void *vexp, void *env) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _throwr_k_kt;
  _data->u._throwr_k._vexp = vexp;
  _data->u._throwr_k._env = env;
  return (void *)_data;
}

void *ktr_procr_k(void *rand, void *env, void *k) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _procr_k_kt;
  _data->u._procr_k._rand = rand;
  _data->u._procr_k._env = env;
  _data->u._procr_k._k = k;
  return (void *)_data;
}

void *ktr_argr_k(void *p, void *k) {
kt* _data = (kt*)malloc(sizeof(kt));
if(!_data) {
  fprintf(stderr, "Out of memory\n");
  exit(1);
}
  _data->tag = _argr_k_kt;
  _data->u._argr_k._p = p;
  _data->u._argr_k._k = k;
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

void valuer__m__of()
{
exp* _c = (exp*)expr;
switch (_c->tag) {
case _const_exp: {
void *n = _c->u._const._n;
v = (void *)n;
pc = &applyr__m__k;
break; }
case _var_exp: {
void *v = _c->u._var._v;
num = (void *)v;
pc = &applyr__m__env;
break; }
case _if_exp: {
void *test = _c->u._if._test;
void *conseq = _c->u._if._conseq;
void *alt = _c->u._if._alt;
k = (void *)ktr_ifr_k(conseq,alt,env,k);
expr = (void *)test;
pc = &valuer__m__of;
break; }
case _mult_exp: {
void *randr1 = _c->u._mult._randr1;
void *randr2 = _c->u._mult._randr2;
k = (void *)ktr_mulr1r_k(randr2,env,k);
expr = (void *)randr1;
pc = &valuer__m__of;
break; }
case _subr1_exp: {
void *rand = _c->u._subr1._rand;
k = (void *)ktr_subr_k(k);
expr = (void *)rand;
pc = &valuer__m__of;
break; }
case _zero_exp: {
void *rand = _c->u._zero._rand;
k = (void *)ktr_zeror_k(k);
expr = (void *)rand;
pc = &valuer__m__of;
break; }
case _letcc_exp: {
void *body = _c->u._letcc._body;
expr = (void *)body;
env = (void *)envrr_extend(k,env);
pc = &valuer__m__of;
break; }
case _throw_exp: {
void *vexp = _c->u._throw._vexp;
void *kexp = _c->u._throw._kexp;
k = (void *)ktr_throwr_k(vexp,env);
expr = (void *)kexp;
pc = &valuer__m__of;
break; }
case _lambda_exp: {
void *body = _c->u._lambda._body;
v = (void *)closr_closure(body,env);
pc = &applyr__m__k;
break; }
case _app_exp: {
void *rator = _c->u._app._rator;
void *rand = _c->u._app._rand;
k = (void *)ktr_procr_k(rand,env,k);
expr = (void *)rator;
pc = &valuer__m__of;
break; }
}
}

void applyr__m__k()
{
kt* _c = (kt*)k;
switch (_c->tag) {
case _emptyr_k_kt: {
void *dismount = _c->u._emptyr_k._dismount;
_trstr *trstr = (_trstr *)dismount;
longjmp(*trstr->jmpbuf, 1);
break; }
case _ifr_k_kt: {
void *conseq = _c->u._ifr_k._conseq;
void *alt = _c->u._ifr_k._alt;
void *envr__ex__ = _c->u._ifr_k._env;
void *kr__ex__ = _c->u._ifr_k._k;
if(v) {
  k = (void *)kr__ex__;
expr = (void *)conseq;
env = (void *)envr__ex__;
pc = &valuer__m__of;

} else {
  k = (void *)kr__ex__;
expr = (void *)alt;
env = (void *)envr__ex__;
pc = &valuer__m__of;

}
break; }
case _mulr1r_k_kt: {
void *randr2 = _c->u._mulr1r_k._randr2;
void *envr__ex__ = _c->u._mulr1r_k._env;
void *kr__ex__ = _c->u._mulr1r_k._k;
k = (void *)ktr_mulr2r_k(v,kr__ex__);
expr = (void *)randr2;
env = (void *)envr__ex__;
pc = &valuer__m__of;
break; }
case _mulr2r_k_kt: {
void *w = _c->u._mulr2r_k._w;
void *kr__ex__ = _c->u._mulr2r_k._k;
k = (void *)kr__ex__;
v = (void *)(void *)((int)w * (int)v);
pc = &applyr__m__k;
break; }
case _subr_k_kt: {
void *kr__ex__ = _c->u._subr_k._k;
k = (void *)kr__ex__;
v = (void *)(void *)((int)v - (int)(void *)1);
pc = &applyr__m__k;
break; }
case _zeror_k_kt: {
void *kr__ex__ = _c->u._zeror_k._k;
k = (void *)kr__ex__;
v = (void *)(v == 0);
pc = &applyr__m__k;
break; }
case _throwr_k_kt: {
void *vexp = _c->u._throwr_k._vexp;
void *envr__ex__ = _c->u._throwr_k._env;
k = (void *)v;
expr = (void *)vexp;
env = (void *)envr__ex__;
pc = &valuer__m__of;
break; }
case _procr_k_kt: {
void *rand = _c->u._procr_k._rand;
void *envr__ex__ = _c->u._procr_k._env;
void *kr__ex__ = _c->u._procr_k._k;
k = (void *)ktr_argr_k(v,kr__ex__);
expr = (void *)rand;
env = (void *)envr__ex__;
pc = &valuer__m__of;
break; }
case _argr_k_kt: {
void *p = _c->u._argr_k._p;
void *kr__ex__ = _c->u._argr_k._k;
c = (void *)p;
a = (void *)v;
k = (void *)kr__ex__;
pc = &applyr__m__proc;
break; }
}
}

void applyr__m__env()
{
envr* _c = (envr*)env;
switch (_c->tag) {
case _empty_envr: {
fprintf(stderr, "unbound variable");
 exit(1);
break; }
case _extend_envr: {
void *arg = _c->u._extend._arg;
void *envr__ex__ = _c->u._extend._env;
if((num == 0)) {
  v = (void *)arg;
pc = &applyr__m__k;

} else {
  env = (void *)envr__ex__;
num = (void *)(void *)((int)num - 1);
pc = &applyr__m__env;

}
break; }
}
}

void applyr__m__proc()
{
clos* _c = (clos*)c;
switch (_c->tag) {
case _closure_clos: {
void *code = _c->u._closure._code;
void *envr__ex__ = _c->u._closure._env;
expr = (void *)code;
env = (void *)envrr_extend(a,envr__ex__);
pc = &valuer__m__of;
break; }
}
}

int main()
{
expr = (void *)expr_mult(expr_const((void *)3),expr_letcc(expr_mult(expr_const((void *)2),expr_throw(expr_const((void *)4),expr_var((void *)0)))));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> (* 3 (letcc q (* 2 (throw 4 q)))): %d\n", (int)v);expr = (void *)expr_mult(expr_const((void *)2),expr_letcc(expr_mult(expr_letcc(expr_throw(expr_const((void *)3),expr_var((void *)1))),expr_const((void *)5))));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> (* 2 (letcc k (* (letcc c (throw 3 k)) 5))): %d\n", (int)v);expr = (void *)expr_app(expr_app(expr_app(expr_lambda(expr_lambda(expr_lambda(expr_mult(expr_var((void *)2),expr_var((void *)0))))),expr_const((void *)5)),expr_const((void *)6)),expr_const((void *)7));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> ((lambda (a b c) (* a c)) 5 6 7): %d\n", (int)v);expr = (void *)expr_const((void *)10);
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> 10: %d\n", (int)v);expr = (void *)expr_mult(expr_const((void *)2),expr_const((void *)3));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> (* 2 3): %d\n", (int)v);expr = (void *)expr_if(expr_zero(expr_const((void *)0)),expr_const((void *)1),expr_const((void *)0));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> (if (zero? 0) 1 0): %d\n", (int)v);expr = (void *)expr_if(expr_zero(expr_const((void *)1)),expr_const((void *)0),expr_const((void *)1));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> (if (zero? 1) 0 1): %d\n", (int)v);expr = (void *)expr_subr1(expr_const((void *)7));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> (sub1 7): %d\n", (int)v);expr = (void *)expr_mult(expr_const((void *)2),expr_letcc(expr_mult(expr_const((void *)5),expr_throw(expr_mult(expr_const((void *)2),expr_const((void *)6)),expr_var((void *)0)))));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> (* 2 (letcc k (* 5 (throw (* 2 6) k)))): %d\n", (int)v);expr = (void *)expr_app(expr_lambda(expr_app(expr_app(expr_var((void *)0),expr_var((void *)0)),expr_const((void *)5))),expr_lambda(expr_lambda(expr_if(expr_zero(expr_var((void *)0)),expr_const((void *)1),expr_mult(expr_var((void *)0),expr_app(expr_app(expr_var((void *)1),expr_var((void *)1)),expr_subr1(expr_var((void *)0))))))));
env = (void *)envrr_empty();
pc = &valuer__m__of;
mount_tram();
printf("value-of -> !5: %d\n", (int)v);}

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
k= (void *)ktr_emptyr_k(dismount);
for(;;) {
pc();
}
}
return 0;
}
