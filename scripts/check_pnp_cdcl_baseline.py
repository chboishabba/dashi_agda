"""Native Z3 SAT tactic via C API (no Python binding required).
Timeout is solver-internal; external campaign timeout also required.
"""
import ctypes as C
from ctypes.util import find_library
from time import perf_counter


def solve(F,n,timeout_ms=1000):
    lib=C.CDLL(find_library('z3') or 'libz3.so.4');P=C.c_void_p;U=C.c_uint;I=C.c_int;S=C.c_char_p
    def fn(name,ret,*args):
        f=getattr(lib,'Z3_'+name);f.restype=ret;f.argtypes=args;return f
    cfg=fn('mk_config',P)();fn('set_param_value',None,P,S,S)(cfg,b'timeout',str(timeout_ms).encode());ctx=fn('mk_context',P,P)(cfg);fn('del_config',None,P)(cfg)
    tactic=fn('mk_tactic',P,P,S)(ctx,b'sat');fn('tactic_inc_ref',None,P,P)(ctx,tactic)
    solver=fn('mk_solver_from_tactic',P,P,P)(ctx,tactic);fn('solver_inc_ref',None,P,P)(ctx,solver)
    try:
        start=perf_counter();lines=['(declare-const x%d Bool)'%i for i in range(n)]
        for c in F:
            if any(not 1<=abs(l)<=n for l in c):raise ValueError('literal')
            terms=['x%d'%(l-1) if l>0 else '(not x%d)'%(-l-1) for l in c];lines.append('(assert %s)'%('(or '+' '.join(terms)+')' if terms else 'false'))
        fn('solver_from_string',None,P,P,S)(ctx,solver,'\n'.join(lines).encode());parsed=perf_counter();q=fn('solver_check',I,P,P)(ctx,solver);done=perf_counter()
        st=fn('solver_get_statistics',P,P,P)(ctx,solver);fn('stats_inc_ref',None,P,P)(ctx,st);stats={}
        for i in range(fn('stats_size',U,P,P)(ctx,st)):
            key=fn('stats_get_key',S,P,P,U)(ctx,st,i).decode();stats[key]=fn('stats_get_uint_value',U,P,P,U)(ctx,st,i) if fn('stats_is_uint',C.c_bool,P,P,U)(ctx,st,i) else fn('stats_get_double_value',C.c_double,P,P,U)(ctx,st,i)
        fn('stats_dec_ref',None,P,P)(ctx,st)
        out=dict(status={-1:'EMPTY',0:'UNKNOWN',1:'WITNESS'}[q],parse_ms=(parsed-start)*1000,solve_ms=(done-parsed)*1000,stats=stats,version=fn('get_full_version',S)().decode())
        if q==1:
            model=fn('solver_get_model',P,P,P)(ctx,solver);fn('model_inc_ref',None,P,P)(ctx,model);sort=fn('mk_bool_sort',P,P)(ctx);x=[]
            for i in range(n):
                sym=fn('mk_string_symbol',P,P,S)(ctx,('x%d'%i).encode());ast=fn('mk_const',P,P,P,P)(ctx,sym,sort);v=P()
                assert fn('model_eval',C.c_bool,P,P,P,C.c_bool,C.POINTER(P))(ctx,model,ast,True,C.byref(v));val=fn('get_bool_value',I,P,P)(ctx,v);assert val in (-1,1);x.append(int(val==1))
            fn('model_dec_ref',None,P,P)(ctx,model);assert all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F);out['witness']=x
        return out
    finally:
        fn('solver_dec_ref',None,P,P)(ctx,solver);fn('tactic_dec_ref',None,P,P)(ctx,tactic);fn('del_context',None,P)(ctx)


if __name__=='__main__':
    print(solve(((1,),(-1,)),1));print(solve(((1,2),),2))
