typedef void (*closure_func_t)(int arg_size, char [arg_size], int env_size, char[env_size]);
typedef struct {int box_ref_count; char box_contents[0]; } box_t;

#define CLOSURE_FUNC(clo)  ((closure_func_t*)clo)
#define CLOSURE_ENV_SIZE(clo)  ((int*)(clo + sizeof(closure_func_t))) 
#define CLOSURE_ENV(clo)  (CLOSURE_ENV_SIZE(clo) + sizeof(int)) 
#define ENV_TO_CLOSURE_SIZE(sz)  (sz +sizeof(int) + sizeof(closure_func_t))
#define CLOSURE_SIZE(clo) (ENV_TO_CLOSURE_SIZE(*CLOSURE_ENV_SIZE(clo)))
#define CLOSURE_CALL(clo,arg_size,arg) (CLOSURE_FUNC(clo))(arg_size,arg,CLOSURE_ENV_SIZE(clo),CLOSURE_ENV(clo))

#define BOX_SIZE (sizeof(box_t*))
#define AS_BOX(box) (*(box_t**)box)
#define BOX_REFCOUNT(box)      (AS_BOX(box)->box_refcount)
#define BOX_CONTENTS(box)      (AS_BOX(box)->box_contents)
#define BOX_DEREF(box) {if (!(--BOX_REFCOUNT(box))) free(AS_BOX(box));}
#define BOX_ALLOC(sz) malloc(sizeof(box_t) + sz)

#define NOP ()
#define ABORT ()
