void *l, *k, *kr__ex__, *v;

void (*pc)();

struct kt;
typedef struct kt kt;
struct kt {
  enum {
    _emptyr_k_kt,
    _innerr_k_kt,
    _outerr_k_kt
  } tag;
  union {
    struct { void *_dismount; } _emptyr_k;
    struct { void *_k; void *_u; } _innerr_k;
    struct { void *_k; void *_l; } _outerr_k;
  } u;
};

void *ktr_emptyr_k(void *dismount);
void *ktr_innerr_k(void *k, void *u);
void *ktr_outerr_k(void *k, void *l);

void remr8r__m__cpsr__m__rir3();
void applyr__m__kr3();
int main();
int mount_tram();

struct _trstr;
typedef struct _trstr _trstr;
struct _trstr {
  jmp_buf *jmpbuf;
  int value;
};

