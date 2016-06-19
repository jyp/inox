typedef void (*closure_func_t)(int arg_size, char [arg_size], int env_size, char[env_size]);

#define CLOSURE_FUNC(clo)  ((closure_func_t*)clo)
#define CLOSURE_ENV_SIZE(clo)  ((int*)(clo + sizeof(closure_func_t))) 
#define CLOSURE_ENV(clo)  (CLOSURE_ENV_SIZE(clo) + sizeof(int)) 
#define ENV_TO_CLOSURE_SIZE(sz)  (sz +sizeof(int) + sizeof(closure_func_t))
#define CLOSURE_SIZE(clo) (ENV_TO_CLOSURE_SIZE(*CLOSURE_ENV_SIZE(clo)))
#define CLOSURE_CALL(clo,arg_size,arg) (CLOSURE_FUNC(clo))(arg_size,arg,CLOSURE_ENV_SIZE(clo),CLOSURE_ENV(clo))

#define NOP ()
#define ABORT ()
