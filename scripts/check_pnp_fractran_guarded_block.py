"""Exact repeated translation block on raw FRACTRAN exponent lanes.

Classical Conway priority semantics; FRACDASH uses an additional signed
state normalization/decode contract. This is not a signed-IR saturation
theorem, nor a general self-quotation compiler. Each rule (guard,delta)
is a reduced fraction on explicit lanes; guard+delta must be nonnegative.
"""
def compile_block(rules,chosen):
    if not chosen:raise ValueError("empty period")
    n=len(rules[0][0]);prefix=[0]*n;need=[0]*n;higher=[]
    for g,d in rules:
        if len(g)!=n or len(d)!=n or any(a<0 or a+v<0 for a,v in zip(g,d)):
            raise ValueError("invalid fraction rule")
    for i in chosen:
        if not 0<=i<len(rules):raise ValueError("rule index")
        g,d=rules[i]
        need=[max(a,b-p) for a,b,p in zip(need,g,prefix)]
        higher.extend(tuple(a-p for a,p in zip(rules[j][0],prefix)) for j in range(i))
        prefix=[a+b for a,b in zip(prefix,d)]
        need=[max(a,-p) for a,p in zip(need,prefix)]
    return tuple(need),tuple(prefix),tuple(higher)

def hits(v,D,g,k):
    # Exists integer j in [0,k-1] such that every lane meets g.
    lo,hi=0,k-1
    for a,d,b in zip(v,D,g):
        if d>0:lo=max(lo,-((a-b)//d))
        elif d<0:hi=min(hi,(a-b)//(-d))
        elif a<b:return False
        if lo>hi:return False
    return lo<=hi

def jump(v,block,k):
    """Exact endpoint iff the named block is the first-enabled trace.
    No per-period traversal; discovery of the repeated block not assumed free.
    """
    need,D,higher=block
    if k<0 or len(v)!=len(D) or any(a<0 for a in v):raise ValueError("invalid input")
    if k==0:return tuple(v)
    if any(a+min(0,(k-1)*d)<g for a,d,g in zip(v,D,need)):return None
    if any(hits(v,D,g,k) for g in higher):return None
    return tuple(a+k*d for a,d in zip(v,D))
