"""Replayable portfolio refusal; not an intrinsic lower-bound certificate."""
import hashlib,json
from check_pnp_source_derived_cover import source_solve
from check_pnp_bit_data_schedule import Clock


def receipt(F,n,rows,target,cap,data_cap=None,**kw):
    source=dict(F=F,n=n,rows=rows,target=target,options=kw)
    key=hashlib.sha256(json.dumps(source,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    data=None if data_cap is None else Clock(data_cap)
    q=source_solve(F,n,rows,target,cap,data_clock=data,**kw)
    return dict(source_digest=key,allowance=cap,data_cap=data_cap,result=q,
                data_charges=None if data is None else dict(data.count),
                scope='selected producer and declared allowance only')


def main():
    n=6;F=tuple((i+1,j+1) for i in range(n) for j in range(i+1,n))
    rows=tuple(tuple(int(i==j) for i in range(n)) for j in range(n));target=(1,)*n
    opts=dict(max_width=3,pin_width=2)
    a=receipt(F,n,rows,target,10000,**opts)
    assert a==receipt(F,n,rows,target,10000,**opts)
    q=a['result'];assert q['status']=='UNKNOWN' and q['high_fill'] and q['cover_width'][0]==6 and q['generators']==0
    b=receipt(F,n,rows,target,20000,**opts)
    assert a['source_digest']==b['source_digest'] and b['result']['witness']==target
    # The identity syndrome fixes every bit; this residual is easy even
    # with high measured width and no nontrivial coordinate symmetry.
    assert all(any(target[abs(l)-1]==int(l>0) for l in c) for c in F)
    c=receipt(((1,),),1,(),(),10**6,data_cap=0)
    assert c['result']['status']=='UNKNOWN' and c['result']['stop']=='frontier_data_clock'
    print(dict(replay=1,high_fill_easy=1,data_refusal=1))
if __name__=='__main__':main()
