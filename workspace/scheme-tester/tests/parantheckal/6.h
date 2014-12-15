void *r__t__exprr__t__, *r__t__envr__t__, *r__t__kr__t__, *r__t__vr__t__, *r__t__numr__t__, *r__t__cr__t__, *r__t__ar__t__;

void (*r__t__pcr__t__)();

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
    _let_exp,
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
    struct { void *_vexp; void *_body; } _let;
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
void *expr_let(void *vexp, void *body);
void *expr_lambda(void *body);
void *expr_app(void *rator, void *rand);

void valuer__m__of();
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
struct kont;
typedef struct kont kont;
struct kont {
  enum {
    _emptyr__m__k_kont,
    _multr__m__kr1_kont,
    _multr__m__kr2_kont,
    _subr1r__m__k_kont,
    _zeror__q__r__m__k_kont,
    _ifr__m__k_kont,
    _cr__m__k_kont,
    _letr__m__k_kont,
    _procr__m__k_kont,
    _argr__m__k_kont
  } tag;
  union {
    struct { void *_dismount; } _emptyr__m__k;
    struct { void *_randr2; void *_env; void *_k; } _multr__m__kr1;
    struct { void *_w; void *_k; } _multr__m__kr2;
    struct { void *_k; } _subr1r__m__k;
    struct { void *_k; } _zeror__q__r__m__k;
    struct { void *_conseq; void *_alt; void *_env; void *_k; } _ifr__m__k;
    struct { void *_vexp; void *_env; } _cr__m__k;
    struct { void *_body; void *_env; void *_k; } _letr__m__k;
    struct { void *_rand; void *_env; void *_k; } _procr__m__k;
    struct { void *_proc; void *_k; } _argr__m__k;
  } u;
};

void *kontr_emptyr__m__k(void *dismount);
void *kontr_multr__m__kr1(void *randr2, void *env, void *k);
void *kontr_multr__m__kr2(void *w, void *k);
void *kontr_subr1r__m__k(void *k);
void *kontr_zeror__q__r__m__k(void *k);
void *kontr_ifr__m__k(void *conseq, void *alt, void *env, void *k);
void *kontr_cr__m__k(void *vexp, void *env);
void *kontr_letr__m__k(void *body, void *env, void *k);
void *kontr_procr__m__k(void *rand, void *env, void *k);
void *kontr_argr__m__k(void *proc, void *k);

void applyr__m__k();
int main();
int mount_tram();

struct _trstr;
typedef struct _trstr _trstr;
struct _trstr {
  jmp_buf *jmpbuf;
  int value;
};

