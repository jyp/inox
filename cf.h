#include <stdlib.h>
#include <string.h>

typedef int A;
typedef int B;


/* Closures */
typedef void (*closure_func_t)(int arg_size, char [arg_size], int env_size, char[env_size]);
typedef struct {
  closure_func_t func;
  int env_size;
  char env[0];
} closure_t;

#define AS_CLOSURE(clo)    (*(closure_t*)(clo))
#define CLOSURE_FUNC(clo)  (AS_CLOSURE(clo).func)
#define CLOSURE_ENV_SIZE(clo)  (AS_CLOSURE(clo).env_size) 
#define CLOSURE_ENV(clo)  (AS_CLOSURE(clo).env) 
#define ENV_TO_CLOSURE_SIZE(sz)  (sz + sizeof(closure_t))
#define CLOSURE_SIZE(clo) (ENV_TO_CLOSURE_SIZE(CLOSURE_ENV_SIZE(clo)))
#define CLOSURE_CALL(clo,arg,arg_size) (CLOSURE_FUNC(clo))(arg_size,arg,CLOSURE_ENV_SIZE(clo),CLOSURE_ENV(clo))

/* Boxes */
typedef struct {int box_ref_count; char box_contents[0]; } box_t;

#define BOX_SIZE (sizeof(box_t*))
#define AS_BOX(box) (*(box_t**)box)
#define BOX_REFCOUNT(box)      (AS_BOX(box)->box_refcount)
#define BOX_CONTENTS(box)      (AS_BOX(box)->box_contents)
#define BOX_DEREF(box) {if (!(--BOX_REFCOUNT(box))) free(AS_BOX(box));}
#define BOX_ALLOC(sz) malloc(sizeof(box_t) + sz)

/* Units */
#define NOP      0;
#define ABORT(x) {printf("ABORT: %s", #x); abort();}
