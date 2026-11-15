#!/usr/bin/env python3
"""F1: exact source coding and standard-TM polynomial clock checks.

Mathematical model-closure proof is in ClayF1StandardHaltingCostModel20261115.md.
These checks illustrate exact universal algebraic inequalities; finite
samples are not a native Agda record construction or theorem by themselves.
"""
from itertools import product

TAG={"Z":"000","S":"001","v":"010","f":"011","t":"100","!":"101","&":"110","|":"111"}
REV={v:k for k,v in TAG.items()}

def code(f):
    op=f[0]
    if op=="v": return TAG["v"]+TAG["S"]*f[1]+TAG["Z"]
    if op in ("t","f"): return TAG[op]
    if op=="!":return TAG["!"]+code(f[1])
    if op in ("&","|"):return TAG[op]+code(f[1])+code(f[2])
    raise ValueError(op)

def decode(bits):
    tokens=[REV[bits[j:j+3]] for j in range(0,len(bits),3)]
    assert len(bits)%3==0
    def parse(i):
        t=tokens[i];i+=1
        if t=="v":
            k=0
            while tokens[i]=="S":k+=1;i+=1
            assert tokens[i]=="Z"
            return ("v",k),i+1
        if t in ("t","f"):return (t,),i
        if t=="!":
            x,i=parse(i);return ("!",x),i
        a,i=parse(i);b,i=parse(i)
        return (t,a,b),i
    f,i=parse(0)
    assert i==len(tokens)
    return f

def rename_first_occurrence(f):
    table={}
    def walk(f):
        t=f[0]
        if t=="v":
            if f[1] not in table:table[f[1]]=len(table)
            return ("v",table[f[1]])
        if t in ("t","f"):return f
        if t=="!":return ("!",walk(f[1]))
        return (t,walk(f[1]),walk(f[2]))
    return walk(f),table

def eval_formula(f,a):
    op=f[0]
    if op=="v":return a[f[1]]
    if op=="t":return True
    if op=="f":return False
    if op=="!":return not eval_formula(f[1],a)
    if op=="&":return eval_formula(f[1],a) and eval_formula(f[2],a)
    return eval_formula(f[1],a) or eval_formula(f[2],a)

def compact(f):
    op=f[0]
    if op=="v":return "v"+format(f[1],"b")+";"
    if op in ("t","f"):return op
    if op=="!":return "!"+compact(f[1])
    return op+compact(f[1])+compact(f[2])

def check_formula(f):
    src=code(f)
    assert decode(src)==f
    assert len(src)%3==0
    norm,table=rename_first_occurrence(f)
    m=len(compact(f))
    assert len(code(norm))<=3*m*(m+2)
    for bits in product([False,True],repeat=len(table)):
        a={var:bits[j] for var,j in table.items()}
        assert eval_formula(f,a)==eval_formula(norm,dict(enumerate(bits)))
    return len(src)

# The standard finite-state two-phase compiler exists independently of the
# test: p_M(n)=a(1+n)^d, m<=n+p_M(n), p_D(m)=b(1+m)^e.
# A bounded number of scans of the O(n+p_M+p_D) used cells per emulated step
# gives at most C(1+n+p_M+p_D)^3 with C depending on the two fixed machines.
# If h=max(1,d), H=h*max(1,e), B=2+a+b(2+a)^e, the clock is
# at most C*B^3*(1+n)^(3H) (for all natural n, a, b, d, e).
def check_clocks(a,b,d,e,n):
    N=n+1
    tm=a*N**d
    m=n+tm
    td=b*(1+m)**e
    h=max(1,d)
    H=h*max(1,e)
    B=2+a+b*(2+a)**e
    assert 1+n+tm+td <= B*N**H
    assert 7*(1+n+tm+td)**3 <= 7*B**3*N**(3*H)

forms=[("t",),("f",),("v",0),("v",1),("v",3),("v",1024),
       ("!",("v",77777)),
       ("&",("v",0),("!",("v",9999))),
       ("|",("&",("v",13),("v",99999)),("!",("v",13)))]
base=[("t",),("f",),("v",0),("v",1),("v",2)]
forms += [("!",f) for f in base]
forms += [(op,x,y) for op in ("&","|") for x in base for y in base]
for f in forms:check_formula(f)
num=0
for a,b,d,e,n in product(range(4),range(4),range(5),range(5),[0,1,2,3,5,8,16]):
    check_clocks(a,b,d,e,n)
    num+=1
print("PASS 8-token original 3-bit canonical formula codec",len(forms),"terms")
print("PASS all-assignment satisfiability equivalence of source variable-renaming")
print("PASS O(m^2) source size bound after compact-binary index alpha-renaming")
print("PASS exact polynomial composition majorant",num,"integer tuples")
print("NOTE universal model-closure proof is mathematical, not the finite tests; native Agda F1 term still owed")
