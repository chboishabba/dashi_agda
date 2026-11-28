"""Independent phase-list specification in normalized blank-first digits.
Compare every actual sparse emitted rule after stable source-tag grouping.
"""
from check_pnp_stack_fractran import compile_stack,Runner,source_next
from check_pnp_stack_priority_transport import audit
from random import Random
from collections import Counter,defaultdict


def normalized_tag(M,t):
    # Restore tags are nested by tuple concatenation in the actual compiler.
    if t[0]=='loop':return (normalized_tag(M,t[1:])[0],True)
    if t[0]=='restore':
        p,_=normalized_tag(M,t[1:]);return (('restoreAction',)+p[1:] if p[0]=='action' else ('restoreLeft',)+p[1:],False)
    if t[0] in ('quot','action','leftquot'):return ((t[0],t[1],M.digit(t[2])),False)
    return (t,False)


def phase_list(M,tag):
    p,mid=tag;name,q,*rest=p;a=rest[0] if rest else None;B=M.base
    table={}
    for v,s,z,b,d in M.rules:table.setdefault((v,M.digit(s)),(z,M.digit(b),d))
    if name in ('action','restoreAction'):
        rule=table.get((q,a));x,b,dst=(1,a,('halt',q)) if rule is None else ((0,rule[1],('rightlen',rule[0])) if rule[2]==1 else (1,rule[1],('leftshift' if rule[2]==-1 else 'q',rule[0])))
    loop={'read':(1,B,2,1),'quot':(2,1,1,1),'leftshift':(1,1,2,B),'restoreLeft':(2,1,1,1),'leftpop':(0,B,2,1),'leftquot':(2,1,0,1)}.get(name)
    if name=='action':loop=(x,1,2,B)
    if name=='restoreAction':loop=(2,1,x,1)
    if mid:return [(p,False,(),())] if loop else []
    def edge(dst,take=(),give=(),mid=False):return (dst,mid,tuple((i,a) for i,a in take if a),tuple((i,a) for i,a in give if a))
    P=[]
    if loop:
        l,c,r,e=loop;P.append(edge(p,((l,c),),((r,e),),True))
    if name=='q':P.append(edge(('read',q)))
    elif name=='read':P.extend(edge(('quot',q,j),((1,j),)) for j in reversed(range(M.symbols)))
    elif name=='quot':P.append(edge(('action',q,a)))
    elif name=='action':P.append(edge(('restoreAction',q,a)))
    elif name=='restoreAction':P.append(edge(dst,(),((x,b),)))
    elif name=='leftshift':P.append(edge(('restoreLeft',q)))
    elif name=='restoreLeft':P.append(edge(('leftpop',q)))
    elif name=='leftpop':P.extend(edge(('leftquot',q,j),((0,j),),((1,j),)) for j in reversed(range(M.symbols)))
    elif name=='leftquot':P.append(edge(('leftlen',q)))
    elif name=='rightlen':P.extend((edge(('rightrestore',q),((4,2),),((3,1),)),edge(('q',q),(),((3,1),))))
    elif name=='rightrestore':P.append(edge(('q',q),(),((4,1),)))
    elif name=='leftlen':P.extend((edge(('q',q),((3,1),),((4,1),)),edge(('q',q),(),((4,1),))))
    elif name!='halt':raise ValueError(tag)
    return P


def main():
    C=Counter()
    for i in range(256):
        r=Random(3692842+i);q=1+i%3;a=1+i%4;blank=i%a
        rules=tuple((r.randrange(q),r.randrange(a),r.randrange(q),r.randrange(a),r.choice((-1,0,1))) for _ in range(i%11))
        M=compile_stack(q,a,blank,rules);out,E=audit(M);tags={j:normalized_tag(M,t) for j,t in enumerate(M.tags) if j>=5}
        assert len(set(tags.values()))==len(tags)
        for p,t in tags.items():
            actual=[(*tags[E[j][1]],tuple(sorted(E[j][2].items())),tuple(sorted(E[j][3].items()))) for j in out.get(p,())]
            assert actual==phase_list(M,t),(t,actual,phase_list(M,t))
            C['phase_lists']+=1;C['edges']+=len(actual)
        # Interleaving is not contiguous in general; stable grouping keeps
        # the same within-tag order and hence the exact enabled successor.
        for p,indices in out.items():
            C['noncontiguous']+=bool(indices) and indices!=list(range(indices[0],indices[-1]+1))
        order=[j for p in sorted(out) for j in out[p]];dense=M.dense();run=Runner(M)
        for p in tags:
            for _ in range(3):
                v=tuple(r.randrange(8) if j<5 else int(j==p) for j in range(len(M.tags)))
                k,u=run.first(v);idx=next((j for j in order if all(a>=b for a,b in zip(v,dense[j][0]))),None)
                assert idx==k;C['priority']+=1
        C['fixtures']+=1
    print(dict(C))
if __name__=='__main__':main()
