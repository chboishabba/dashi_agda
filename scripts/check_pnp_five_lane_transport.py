"""Replay full normalized phase emitter, including digit and extent exits.
Independent five-lane arithmetic; compare original sparse priority runner.
"""
from check_pnp_emitted_phase_campaign import phase_list,normalized_tag
from check_pnp_stack_fractran import compile_stack,Runner,source_next
from random import Random
from collections import Counter


def grouped(M,v):
    tags={normalized_tag(M,t):j for j,t in enumerate(M.tags) if j>=5}
    p=next(t for t,j in tags.items() if v[j]);data=list(v[:5]);raw=0;jumps=0;exits=0
    if p[0][0]=='halt':return v,True,raw,jumps,exits
    while True:
        E=phase_list(M,p);assert E
        dst,mid,take,give=E[0]
        if mid and dst==p[0] and not p[1]:
            assert phase_list(M,(dst,True))==[(p[0],False,(),())]
            ((x,a),),((y,b),)=take,give;assert x!=y and a>0
            k=data[x]//a
            if k:
                before=data[:];data[x]-=a*k;data[y]+=b*k
                assert data[x]==before[x]%a and all(data[i]==before[i] for i in range(5) if i not in (x,y))
                raw+=2*k;jumps+=1
            E=E[1:]
        dst,mid,take,give=next(e for e in E if all(data[i]>=a for i,a in e[2]))
        for i,a in take:data[i]-=a
        for i,a in give:data[i]+=a
        raw+=1;exits+=1;p=(dst,mid)
        if not mid and dst[0] in ('q','halt'):
            out=tuple(data+[int(j==tags[p]) for j in range(5,len(M.tags))]);assert data[2]==0 and data[4]>=1 and data[0]<M.base**data[3] and data[1]<M.base**data[4]
            return out,dst[0]=='halt',raw,jumps,exits


def main():
    C=Counter()
    for i in range(256):
        g=Random(3692845+i);Q=1+i%3;A=1+i%4;blank=i%A
        rules=tuple((g.randrange(Q),g.randrange(A),g.randrange(Q),g.randrange(A),g.choice((-1,0,1))) for _ in range(i%11));M=compile_stack(Q,A,blank,rules);run=Runner(M)
        for _ in range(4):
            c=(g.randrange(Q),tuple(g.randrange(A) for _ in range(g.randrange(4))),tuple(g.randrange(A) for _ in range(1+g.randrange(4))))
            v=M.encode(*c);u,h,k,j,e=grouped(M,v);z,h2,S=run.step(v,False,100000)
            assert (u,h,k)==(z,h2,S['raw']);x=source_next(M,c);assert M.decode(u)[:3]==(c if x is None else x) and h==(x is None)
            C.update(endpoints=1,raw=k,jumps=j,exits=e,halts=int(h))
        C['programs']+=1
    M=compile_stack(1,3,0,((0,1,0,2,-1),));v=M.encode(0,(2,)*128,(1,)*128);u,h,k,j,e=grouped(M,v);z,h2,S=Runner(M).step(v);assert (u,h,k)==(z,h2,S['raw'])
    print(dict(C,huge=dict(raw=str(k),jumps=j,exits=e,fractions=len(M.sparse))))
if __name__=='__main__':main()
