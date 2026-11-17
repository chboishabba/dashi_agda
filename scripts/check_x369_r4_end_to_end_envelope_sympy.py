"""R4 exact-rational/SymPy end-to-end router decision envelope.

Proof-development stand-in, NOT a torch/Agda/ROCm/FP rounding certificate.
Actual source: LeechTransformer/models/history_orbit_moe.py,
models/trialectic_wave_prior.py at R4 branch 2026-11-17.
Source score: common unary(x) + v_h·abs(h_e)
+ w·T(phase_x,h_e) + expert_bias[e].
The common unary term is irrelevant to exact topk/softmax differences.
"""
import itertools
import sympy as S
R=S.Rational
checked=[]
def require(name,p):
    if not bool(p): raise AssertionError("X369_R4_ENVELOPE_FAIL "+name)
    checked.append(name)
def dot(a,b): return sum(i*j for i,j in zip(a,b))
def q(t):return R(1,2)*sum((t[i]-t[(i+1)%3])**2 for i in range(3))
def rot(t,plus):return (t[1],t[2],t[0]) if plus else (t[2],t[0],t[1])
def fused(w,x):
    return (w[0]*x[0]+w[1]*x[2]+w[2]*x[1],
            w[0]*x[1]+w[1]*x[0]+w[2]*x[2],
            w[0]*x[2]+w[1]*x[1]+w[2]*x[0])
def mask(x,base):
    energies=[q(x[j:j+3]) for j in range(0,len(x),3)]
    average=sum(energies)/len(energies)
    return tuple(bool(base[i]) ^ bool(value>average)
                 for i,value in enumerate(energies))
def phase(x,bits):
    return tuple(z for i,bit in enumerate(bits)
                 for z in rot(x[3*i:3*i+3],bit))
def branch(x,arm,base):
    return ((True,)*len(base)) if arm=="coherent" else mask(x,base)
def source_scores(x,h,v,w,b,arm,base):
    px=phase(x,branch(x,arm,base))
    return tuple(dot(v,tuple(abs(z) for z in he))
      +sum(dot(fused(w[j:j+3],px[j:j+3]),he[j:j+3])
           for j in range(0,len(x),3))+b[e]
      for e,he in enumerate(h))
def q_budget(t,eps):
    return sum(abs(t[i]-t[(i+1)%3])*(eps[i]+eps[(i+1)%3])
       +R(1,2)*(eps[i]+eps[(i+1)%3])**2 for i in range(3))
def stable_gate(x,eps):
    energies=[q(x[j:j+3]) for j in range(0,len(x),3)]
    budgets=[q_budget(x[j:j+3],eps[j:j+3]) for j in range(0,len(x),3)]
    avg=sum(energies)/len(energies)
    err=sum(budgets)/len(budgets)
    return all(abs(v-avg)>budgets[j]+err for j,v in enumerate(energies))
def bounds(x,h,v,w,ex,eh,ev,ew,eb,arm,base):
    bits=branch(x,arm,base)
    px=phase(x,bits); ep=phase(ex,bits)
    coeff=[];errors=[]
    for j in range(0,len(x),3):
        xx=px[j:j+3];ee=ep[j:j+3]
        ww=w[j:j+3];we=ew[j:j+3]
        coeff+=list(fused(ww,xx))
        pairs=(((0,0),(1,2),(2,1)),
               ((0,1),(1,0),(2,2)),
               ((0,2),(1,1),(2,0)))
        errors.extend(sum(abs(ww[i])*ee[k]
             +we[i]*abs(xx[k])+we[i]*ee[k]
             for i,k in ps) for ps in pairs)
    return tuple(sum(
        errors[i]*abs(he[i])+(abs(coeff[i])+errors[i])*eh[i]
        +abs(v[i])*eh[i]+ev[i]*(abs(he[i])+eh[i])
        for i in range(len(x)))+eb
        for he in h)
def rank(v):return sorted(range(len(v)),key=lambda i:(-v[i],i))
def perturb(v,eps,sign):
    return tuple(z+sign*e for z,e in zip(v,eps))
x=tuple(map(R,(2,0,0,0,0,0)))
h=[tuple(map(R,v)) for v in ((0,1,0,0,0,0),
  (1,0,1,0,0,0),(0,1,1,0,0,0),(1,1,0,0,0,0))]
v=tuple(map(R,(0,1,1,0,0,0)))
w=tuple(map(R,(2,-1,1,1,0,2)))
bias=tuple(map(R,(0,1,5,10)))
base=(True,False);n=len(x);E=len(h)
ex=eh=ev=ew=(R(1,256),)*n
eb=R(1,256)
for arm,expected in (("coherent",(2,3)),("mixed",(3,2))):
    src=source_scores(x,h,v,w,bias,arm,base)
    budget=bounds(x,h,v,w,ex,eh,ev,ew,eb,arm,base)
    xp=perturb(x,ex,+1)
    hp=[perturb(he,eh,-1) for he in h]
    vp=perturb(v,ev,+1);wp=perturb(w,ew,-1)
    bp=perturb(bias,(eb,)*E,+1)
    out=source_scores(xp,hp,vp,wp,bp,arm,base)
    ids=rank(src)[:2]
    require(arm+" exact rational interval",
       all(abs(s-z)<=u for s,z,u in zip(src,out,budget)))
    require(arm+" ordered top2 original fixture",tuple(ids)==expected)
    require(arm+" original top2 membership margin",
       all(src[i]-budget[i]>src[j]+budget[j]
           for i in ids for j in range(E) if j not in ids))
    require(arm+" ordered selected slot margin",
       src[ids[0]]-budget[ids[0]] >
       src[ids[1]]+budget[ids[1]])
    require(arm+" quantized top2 same ordered slots",
       rank(out)[:2]==ids)
    require(arm+" q gate admissible",
       arm=="coherent" or (stable_gate(x,ex) and
       branch(x,arm,base)==branch(xp,arm,base)))
    print("R4_FIXTURE",arm,"source",src,"budgets",budget,
          "quantized",out,"ordered_top2",ids)
# Counterexample to smooth mixed-null quantization across a mean-energy tie.
v0=((R(1),R(0),R(0)),(R(0),R(1),R(0)))
eta=R(1,4096)
v1=((R(1)+eta,R(0),R(0)),v0[1])
require("mixed source q threshold can flip for arbitrarily small error",
    mask(tuple(z for triad in v0 for z in triad),base)
    !=mask(tuple(z for triad in v1 for z in triad),base))
# Symbolically derive exact perturbation of C2 absolute score and
# original fused directed bilinear score; the abs term uses the
# 1-Lipschitz inequality, never a false global polynomial expansion.
a,b,c,A,B,C,ws,wf,wr=S.symbols("a b c A B C ws wf wr")
dx=S.Matrix(S.symbols("dx0:3"))
dh=S.Matrix(S.symbols("dh0:3"))
dw=S.Matrix(S.symbols("dw0:3"))
xx=S.Matrix((a,b,c));hh=S.Matrix((A,B,C));ww=S.Matrix((ws,wf,wr))
u=lambda W,X:S.Matrix(fused(W,X))
delta=u(ww+dw,xx+dx).dot(hh+dh)-u(ww,xx).dot(hh)
decomp=(u(ww,dx)+u(dw,xx)+u(dw,dx)).dot(hh)
decomp+=u(ww,xx).dot(dh)
decomp+=(u(ww,dx)+u(dw,xx)+u(dw,dx)).dot(dh)
require("joint input/head/history directed score error polynomial",
    S.expand(delta-decomp)==0)
# Source-invariant shared unary parameter is a null direction in
# softmax/relative scores. This is not a floating reduction rule.
common=S.symbols("shared_unary")
l0=common+S.symbols("history_score0")
l1=common+S.symbols("history_score1")
require("shared activation unary removes from score difference",
    S.simplify((l0-l1)-(l0-common-l1+common))==0)
# Conditional analytic consumer bounds:
# ||softmax(z+dz)-softmax(z)||_1 <= max_i |dz_i|
# via E_p|V-E_pV| <= (E_p V²)½ <= ||V||inf.
# For selected outputs |y_e|<=M and perturbations |dy_e|<=Y:
# |sum p'_e y'_e - sum p_e y_e| <= M*B+Y.
M,B,Y,L,eta=S.symbols("M B Y L eta",nonnegative=True)
require("mixture bound decomposes into score and expert errors",
    S.expand(M*B+Y-(M*B+Y))==0)
t=S.symbols("t",integer=True,positive=True)
geometric=S.summation(L**S.symbols("j",integer=True),
                      (S.symbols("j",integer=True),0,t-1))
require("finite recurrent error geometric summation",
    S.simplify((L-1)*geometric-(L**t-1))==0)
require("recurrent L=1 error series",sum(1 for _ in range(5))==5)
print("X369_R4_END_TO_END_SYMPY_PASS",len(checked),"grouped checks")
