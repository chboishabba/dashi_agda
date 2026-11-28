"""Static priority audit of the actual fixed FRACTRAN compiler.
One-hot control makes global first-match equal to the source-phase sublist.
At canonical boundaries stacks have exact extent; private scratch phases
use a separate invariant. This is not a same-target standard tape clock.
"""
from check_pnp_stack_fractran import compile_stack,Runner,source_next
from check_pnp_fractran_guarded_block import jump
from collections import defaultdict


def audit(M):
    outgoing=defaultdict(list);edges=[]
    for k,(num,den) in enumerate(M.sparse):
        src=[i for i in den if i>=5];dst=[i for i in num if i>=5]
        assert len(src)==len(dst)==1 and den[src[0]]==num[dst[0]]==1
        assert not set(num)&set(den) and all(a>0 for a in tuple(num.values())+tuple(den.values()))
        p,q=src[0],dst[0];outgoing[p].append(k);edges.append((p,q,{i:a for i,a in den.items() if i<5},{i:a for i,a in num.items() if i<5}))
    for p,(k,x,a) in M.loops.items():
        src,mid,take,give=edges[k];back,dst,bt,bg=edges[k+1]
        assert src==dst==p and mid==back and mid!=p and outgoing[mid]==[k+1]
        assert outgoing[p][0]==k and len(outgoing[p])>=2
        assert take=={x:a} and len(give)==1 and not bt and not bg
        y,b=next(iter(give.items()));assert x!=y and a>0 and b>0
    for i,tag in enumerate(M.tags[5:],5):
        assert bool(outgoing[i])==(tag[0]!='halt')
    return dict(outgoing),tuple(edges)


def phase(M,v):
    assert len(v)==len(M.tags) and all(a>=0 for a in v) and sum(v[5:])==1
    p=next(i for i in range(5,len(v)) if v[i]);return p


def boundary(M,v):
    p=phase(M,v);assert M.tags[p][0] in ('q','halt')
    assert v[2]==0 and v[4]>=1 and v[0]<M.base**v[3] and v[1]<M.base**v[4]
    return M.tags[p]


def numeric(M,v):
    """Independent expected packed source transition, no full list decode."""
    tag,q=boundary(M,v);L,R,_,ln,rn=v[:5];B=M.base
    if tag=='halt':return v,True
    a=M.symbol(R%B);assert 0<=a<M.symbols;out=list(v);out[5:]=[0]*(len(v)-5)
    for p,s,t,b,d in M.rules:
        if (p,s)!=(q,a):continue
        b=M.digit(b);tail=R//B
        if d==1:out[:5]=[B*L+b,tail,0,ln+1,max(1,rn-1)]
        elif d==0:out[:5]=[L,B*tail+b,0,ln,rn]
        else:out[:5]=[L//B,B*(B*tail+b)+L%B,0,max(0,ln-1),rn+1]
        out[M.tags.index(('q',t))]=1
        return tuple(out),False
    out[M.tags.index(('halt',q))]=1;return tuple(out),True


class AuditedRunner(Runner):
    def __init__(self,M):
        super().__init__(M);self.out,self.edges=audit(M)
    def first_local(self,v):
        p=phase(self.M,v)
        for k in self.out.get(p,()):
            _,q,take,give=self.edges[k]
            if all(v[i]>=a for i,a in take.items()):
                u=list(v);u[p]=0;u[q]=1
                for i,a in take.items():u[i]-=a
                for i,a in give.items():u[i]+=a
                return k,tuple(u)
        return None,None
    def exact(self,v,accelerate=True):
        M=self.M;tag,_=boundary(M,v);want=numeric(M,v);raw=jumps=literal=checks=0
        if tag=='halt':return v,True,dict(raw=0,jumps=0,literal=0,checks=0)
        # Loose private-phase bound. Actual exact extent is checked at
        # each canonical boundary, never falsely imposed mid-transfer.
        limit=M.base**(max(v[3],v[4])+2)
        while True:
            p=phase(M,v);assert max(v[:3])<limit
            info=M.loops.get(p)
            if accelerate and info:
                k,x,a=info;t=v[x]//a
                if t:
                    _,_,take,give=self.edges[k];y,b=next(iter(give.items()))
                    u=list(v);u[x]-=a*t;u[y]+=b*t;u=tuple(u)
                    assert jump(v,self.blocks[p],t)==u and jump(v,self.blocks[p],t+1) is None
                    assert self.first_local(v)[0]==k and self.first_local(u)[0]!=k
                    phase(M,u);assert max(u[:3])<limit
                    v=u;raw+=2*t;jumps+=1;checks+=2;continue
            k,u=self.first_local(v);assert (k,u)==self.first(v) and u is not None
            v=u;raw+=1;literal+=1;p=phase(M,v);assert max(v[:3])<limit
            if M.tags[p][0] in ('q','halt'):
                tag,_=boundary(M,v);h=tag=='halt';assert (v,h)==want
                return v,h,dict(raw=raw,jumps=jumps,literal=literal,checks=checks)
