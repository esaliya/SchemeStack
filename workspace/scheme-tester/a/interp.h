void *expr, *env, *k, *v, *num, *c, *a;

void (*pc)();

struct exp;
typedef struct exp exp;
struct exp {
  enum {
    _const_exp,
    _var_exp,
    _if_exp,
    _mult_exp,
    _subr1_exp,
    _zero_exp,
    _letcc_exp,
    _throw_exp,
    _lambda_exp,
    _app_exp
  } tag;
  union {
    struct { void *_n; } _const;
    struct { void *_v; } _var;
    struct { void *_test; void *_conseq; void *_alt; } _if;
    struct { void *_randr1; void *_randr2; } _mult;
    struct { void *_rand; } _subr1;
    struct { void *_rand; } _zero;
    struct { void *_body; } _letcc;
    struct { void *_vexp; void *_kexp; } _throw;
    struct { void *_body; } _lambda;
    struct { void *_rator; void *_rand; } _app;
  } u;
};

void *expr_const(void *n);
void *expr_var(void *v);
void *expr_if(void *test, void *conseq, void *alt);
void *expr_mult(void *randr1, void *randr2);
void *expr_subr1(void *rand);
void *expr_zero(void *rand);
void *expr_letcc(void *body);
void *expr_throw(void *vexp, void *kexp);
void *expr_lambda(void *body);
void *expr_app(void *rator, void *rand);

void valuer__m__of();
struct kt;
typedef struct kt kt;
struct kt {
  enum {
    _emptyr_k_kt,
    _ifr_k_kt,
    _mulr1r_k_kt,
    _mulr2r_k_kt,
    _subr_k_kt,
    _zeror_k_kt,
    _throwr_k_kt,
    _procr_k_kt,
    _argr_k_kt
  } tag;
  union {
    struct { void *_dismount; } _emptyr_k;
    struct { void *_conseq; void *_alt; void *_env; void *_k; } _ifr_k;
    struct { void *_randr2; void *_env; void *_k; } _mulr1r_k;
    struct { void *_w; void *_k; } _mulr2r_k;
    struct { void *_k; } _subr_k;
    struct { void *_k; } _zeror_k;
    struct { void *_vexp; void *_env; } _throwr_k;
    struct { void *_rand; void *_env; void *_k; } _procr_k;
    struct { void *_p; void *_k; } _argr_k;
  } u;
};

void *ktr_emptyr_k(void *dismount);
void *ktr_ifr_k(void *conseq, void *alt, void *env, void *k);
void *ktr_mulr1r_k(void *randr2, void *env, void *k);
void *ktr_mulr2r_k(void *w, void *k);
void *ktr_subr_k(void *k);
void *ktr_zeror_k(void *k);
void *ktr_throwr_k(void *vexp, void *env);
void *ktr_procr_k(void *rand, void *env, void *k);
void *ktr_argr_k(void *p, void *k);

void applyr__m__k();
struct envr;
typedef struct envr envr;
struct envr {
  enum {
    _empty_envr,
    _extend_envr
  } tag;
  union {
    struct { char dummy; } _empty;
    struct { void *_arg; void *_env; } _extend;
  } u;
};

void *envrr_empty();
void *envrr_extend(void *arg, void *env);

void applyr__m__env();
struct clos;
typedef struct clos clos;
struct clos {
  enum {
    _closure_clos
  } tag;
  union {
    struct { void *_code; void *_env; } _closure;
  } u;
};

void *closr_closure(void *code, void *env);

void applyr__m__proc();
int main();
int mount_tram();

struct _trstr;
typedef struct _trstr _trstr;
struct _trstr {
  jmp_buf *jmpbuf;
  int value;
};

