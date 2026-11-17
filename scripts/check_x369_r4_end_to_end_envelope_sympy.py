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
    # Exact real softmax on ordered selected IDs; source torch.topk tie
    # semantics are only certified when the listed margins are strict.
    pp=[S.exp(src[i])/sum(S.exp(src[j]) for j in ids) for i in ids]
    qq=[S.exp(out[i])/sum(S.exp(out[j]) for j in ids) for i in ids]
    tv=S.N(sum(S.Abs(pi-qi) for pi,qi in zip(pp,qq)),40)
    Bmax=max(budget[i] for i in ids)
    require(arm+" exact softmax within max selected score budget",
        tv <= Bmax)
    # The one-step selected output mixture is a consumer of scores AND
    # expert outputs; the latter are fixed here, so ||sum(p'-p)y|| <= M B.
    expert_output={ids[0]:R(3),ids[1]:R(-2)}
    out_delta=S.N(S.Abs(sum((qi-pi)*expert_output[i]
                 for i,pi,qi in zip(ids,pp,qq))),40)
    require(arm+" one-step mixture envelope with fixed expert output",
       out_delta<=max(abs(t) for t in expert_output.values())*Bmax)

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
# Matched R4 C2-residual control has a DIFFERENT score
#   (baseline history v + C2 residual history z)·abs(h_e)+expert_bias[e].
# Shared x-only portions cancel. This controls active history capacity
# without pretending its semantic/phase features equal C3.
z=tuple(map(R,(1,-1,2,0,1,-2)))
ez=(R(1,256),)*n
def c2_scores(hist,v,z,b):
    return tuple(dot(tuple(v[i]+z[i] for i in range(n)),
                     tuple(abs(t) for t in he))+b[e]
                 for e,he in enumerate(hist))
def c2_bounds(hist,v,z,eh,ev,ez,eb):
    return tuple(sum(abs(v[i]+z[i])*eh[i]
          +(ev[i]+ez[i])*(abs(he[i])+eh[i])
                 for i in range(n))+eb for he in hist)
c2a=c2_scores(h,v,z,bias)
c2b=c2_scores([perturb(he,eh,-1) for he in h],
              perturb(v,ev,+1),perturb(z,ez,-1),
              perturb(bias,(eb,)*E,+1))
c2B=c2_bounds(h,v,z,eh,ev,ez,eb)
require("matched C2 control full history/bias rational interval",
    all(abs(a-b)<=bb for a,b,bb in zip(c2a,c2b,c2B)))
c2ids=rank(c2a)[:2]
require("matched C2 control top2 strict membership",
    all(c2a[i]-c2B[i]>c2a[j]+c2B[j]
        for i in c2ids for j in range(E) if j not in c2ids))
require("matched C2 control ordered top2 strict",
    c2a[c2ids[0]]-c2B[c2ids[0]] >
    c2a[c2ids[1]]+c2B[c2ids[1]])
require("matched C2 control ordered IDs preserved",
    c2ids==rank(c2b)[:2])
print("R4_FIXTURE c2_control","source",c2a,"budgets",c2B,
      "quantized",c2b,"ordered_top2",c2ids)

# Counterexample to smooth mixed-null quantization across a mean-energy tie.
v0=((R(1),R(0),R(0)),(R(0),R(1),R(0)))
eta=R(1,4096)
v1=((R(1)+eta,R(0),R(0)),v0[1])
require("mixed source q threshold can flip for arbitrarily small error",
    mask(tuple(z for triad in v0 for z in triad),base)
    !=mask(tuple(z for triad in v1 for z in triad),base))
# Source orientation is 2*linear([x,h],orientation.weight,None).
# With input/history and orientation-weight perturbations it has a
# separate chart-sign budget. At inference, certify |score|>budget to
# preserve the +/- sign; equality uses first-nonzero fallback and is NOT
# covered. This is independent of topk membership and q-gate stability.
def orientation_score(z,weight):
    return 2*dot(z,weight)
def orientation_budget(z,weight,ez,ew):
    return 2*sum(abs(weight[i])*ez[i]
        +ew[i]*(abs(z[i])+ez[i]) for i in range(len(z)))
orientation=tuple(map(R,(1,-2,2,0,1,-1,1,0,0,-1,0,2)))
z0=x+h[2]
ez0=ex+eh
ew0=(R(1,256),)*len(z0)
ori0=orientation_score(z0,orientation)
orib=orientation_budget(z0,orientation,ez0,ew0)
ori1=orientation_score(perturb(z0,ez0,+1),
                       perturb(orientation,ew0,-1))
require("orientation score quantization interval",
        abs(ori1-ori0)<=orib)
require("selected expert strict orientation chart margin",
        abs(ori0)>orib and (ori0>0)==(ori1>0))
# Arbitrarily near zero an orientation sign can flip while selected
# route stays unchanged; first-nonzero tie fallback needs separate
# equality/lexicographic certification.
tau=R(1,4096)
require("orientation tie discontinuity negative control",
        orientation_score((tau,),(R(1),))>0 and
        orientation_score((-tau,),(R(1),))<0)
# Conditional recurrence after topk + orientation charts are stable:
# one-step mixture <= M*B+Y; next-layer state error admitted as
# D_(t+1)<=L*D_t+eta. For D_0=0, closed form
# eta*(1+L+...+L^(t-1)); with L=1 it is eta*t.
lam,eta_sym=S.symbols("lam eta",nonnegative=True)
for horizon in range(1,10):
    d=R(0)
    for _ in range(horizon):d=lam*d+eta_sym
    closed=eta_sym*sum(lam**j for j in range(horizon))
    require("conditional recurrence bound unroll n="+str(horizon),
            S.expand(d-closed)==0)

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
# Source nn.GELU() uses the exact default Gaussian GELU. Its
# derivative is Phi(t)+t*phi(t), admitting a global coarse bound
# |GELU'(t)| <= 1 + 1/sqrt(2*pi*e), since 0<=Phi<=1
# and max |t*phi(t)|=1/sqrt(2*pi*e).
# SymPy checks the derivative IDENTITIES, not the global inequality
# or the source's finite-precision erf implementation.
T=S.symbols("T",real=True)
gelu=T*(1+S.erf(T/S.sqrt(2)))/2
phi=S.exp(-T**2/2)/S.sqrt(2*S.pi)
Phi=(1+S.erf(T/S.sqrt(2)))/2
require("source exact GELU derivative factorization",
    S.simplify(S.diff(gelu,T)-(Phi+T*phi))==0)
require("gaussian derivative extremum at |t|=1",
    S.simplify(S.diff(T*phi,T).subs(T,1))==0)
# Reuse early LeechGELUParityHistoricalSafetySteelman20261031:
# exact real GELU reflection and the sharp derivative extremum at
# ±sqrt2. This replaces the loose 1+1/sqrt(2*pi*e) majorant.
Lg=(1+S.erf(1))/2+S.exp(-1)/S.sqrt(S.pi)
require("sharp source GELU global Lipschitz",
    S.simplify(S.diff(gelu,T).subs(T,S.sqrt(2))-Lg)==0
    and bool(Lg>1)
    and bool(Lg<1+1/S.sqrt(2*S.pi*S.E)))
Leven=Lg-S.Rational(1,2)
require("even GELU parity Lipschitz coefficient",
    S.simplify(S.diff(T*S.erf(T/S.sqrt(2))/2,T)
                .subs(T,S.sqrt(2))-Leven)==0)
# For fixed selected IDs and stable orientation charts, Euclidean
# FFN bound Y_e <= ||W2||2 * Lg * ||W1||2
#                  * sqrt(dx²+dh²) + eta_FFN_e
# and cap-projected transition bound H'_e <=
# ||Transition||2 * sqrt(dx²+dh²+Y_e²) + eta_T_e.
# These are conditional operator-norm formulae: the actual
# checkpoint spectral norms and rounding epsilons are NOT available.
Wx,Wy,Tr,Dx,Dh,ef,et=S.symbols(
    "Wx Wy Tr Dx Dh ef et",nonnegative=True)
FFN=Wx*Wy*Lg*S.sqrt(Dx**2+Dh**2)+ef
Ht=Tr*S.sqrt(Dx**2+Dh**2+FFN**2)+et
require("conditional selected expert FFN/transition envelope",
    S.simplify(Ht-(Tr*S.sqrt(Dx**2+Dh**2+FFN**2)+et))==0)

# Actual softmax Jacobian/coupled-score consumer algebra, for three
# ordered selected experts. Shared shifts are a true exact-null
# direction in real arithmetic, even though original torch floating
# reassociation and topk ties are separately guarded.
p0,p1,p2=S.symbols("p0 p1 p2",real=True)
d0,d1,d2=S.symbols("d0 d1 d2",real=True)
ps=S.Matrix((p0,p1,p2))
deltas=S.Matrix((d0,d1,d2))
J=S.diag(*ps)-ps*ps.T
require("softmax Jacobian annihilates common shift on simplex",
    all(S.simplify(z.subs(p2,1-p0-p1))==0
        for z in J*S.ones(3,1)))
mu=(ps.T*deltas)[0]
variance=(ps.T*S.Matrix([di**2 for di in deltas]))[0]-mu**2
centered=sum(ps[i]*(deltas[i]-mu)**2 for i in range(3))
require("softmax Jacobian variance exact identity on simplex",
    S.simplify((variance-centered).subs(p2,1-p0-p1))==0)
# For pi>=0,sum pi=1 and |delta_i|<=B:
# ||J delta||_1 = sum pi|delta_i-mu|
#   <=sqrt(sum pi(delta_i-mu)^2)
#   <=sqrt(sum pi delta_i^2) <= B.
# Integrating the bound along the same selected-score path gives
# ||softmax(s+delta)-softmax(s)||_1<=B.
yp0,yp1,yn0,yn1=S.symbols("yp0 yp1 yn0 yn1",real=True)
pp0,pp1,pn0,pn1=S.symbols("pp0 pp1 pn0 pn1",real=True)
full_out=(pn0*yn0+pn1*yn1)-(pp0*yp0+pp1*yp1)
split_out=((pn0-pp0)*yp0+(pn1-pp1)*yp1
           +pn0*(yn0-yp0)+pn1*(yn1-yp1))
require("output difference splits into softmax and FFN errors",
    S.expand(full_out-split_out)==0)
# Source history transition is computed before output weights:
# use symbolic functions rather than confusing equality with
# a claim about arbitrary external callbacks or selected packets.
xv,hv,pe=S.symbols("xv hv pe",real=True)
expert_ffn=S.Function("expert_ffn")
history_step=S.Function("history_transition")
selected_h=history_step(xv,hv,expert_ffn(xv,hv))
selected_out=pe*expert_ffn(xv,hv)
require("selected expert history is exactly weight-independent",
    S.diff(selected_h,pe)==0)
require("selected expert output carries mixture weight",
    S.diff(selected_out,pe)==expert_ffn(xv,hv))
# General nonautonomous recurrence conditional on all gate/route
# margins re-certified along each input trajectory.
Dstart=S.symbols("Dstart")
Ltime=S.symbols("L0:4",nonnegative=True)
etime=S.symbols("eta0:4",nonnegative=True)
step=Dstart
for k in range(4):step=Ltime[k]*step+etime[k]
closed=Dstart*S.prod(Ltime)
closed+=sum(etime[j]*S.prod(Ltime[k] for k in range(j+1,4))
            for j in range(4))
require("four-step variable-L conditional recurrence exact expansion",
    S.expand(step-closed)==0)

# GELU parity chart alternative: exact real FFN
# F(z)=W2*GELU(W1 z+b1)+b2. For the ORIGINAL signed chart:
# y_sigma(z)=sigma F(sigma z)=O_F(z)+sigma E_F(z)
# (sigma=±1), with chart-flip jump 2 E_F. The earlier
# LeechOddOnlyApproximationObstructionExact donor explains why
# removing the even component is not a generic exact solution.
# The original history transition is affine on
# (sigma h, sigma x, F(sigma z)), followed by sign restoration,
# so H_sigma=Th h+Tx x+Ty y_sigma+sigma bT (before cap).
# This yields chart jump 2(Ty E_F+bT), NOT an arbitrary error.
zsym,bsym,msym,bout=S.symbols("zsym bsym msym bout",real=True)
geluf=lambda zz:zz*(1+S.erf(zz/S.sqrt(2)))/2
Fchart=lambda zz:msym*geluf(zz+bsym)+bout
Fpositive=Fchart(zsym)
Fnegative=Fchart(-zsym)
Echart=(Fpositive+Fnegative)/2
Ochart=(Fpositive-Fnegative)/2
require("original oriented FFN two-sign parity",
    S.simplify(Fpositive-(Ochart+Echart))==0
    and S.simplify(-Fnegative-(Ochart-Echart))==0)
require("learned biased source chart flip is exactly 2 even",
    S.simplify(Fpositive+Fnegative-2*Echart)==0)
Th,Tx,Ty,bT,xscalar,hscalar=S.symbols(
    "Th Tx Ty bT xscalar hscalar",real=True)
Hp=Th*hscalar+Tx*xscalar+Ty*Fpositive+bT
Hn=Th*hscalar+Tx*xscalar-Ty*Fnegative-bT
require("original affine history chart jump",
    S.simplify(Hp-Hn-2*(Ty*Echart+bT))==0)
# Bound on EVEN projection centered at F(0) from GELU curvature:
# |E_F(z)-F(0)| <= ||W2|| min(
#   (Lg-1/2)*||W1 z||,
#   ||W1 z||²/sqrt(2*pi)).
# We do not claim this bounds the bias F(0) without checkpoint data.
require("GELU curvature exact for quadratic chart budget",
    S.simplify(S.diff(geluf(zsym),zsym,2)
       -(2-zsym*zsym)*S.exp(-zsym*zsym/2)/S.sqrt(2*S.pi))==0)
# R4 one-step signed-output and history difference may now be
# bounded with a chart RESIDUAL instead of strict sign preservation:
# Y_e <= Lffn||dz||+2*flip||E_F(z')||+eta_FFN.
# H_e'<=||Th||||dh||+||Tx||||dx||+||Ty|| Y_e
#          +2*flip||bT||+eta_transition
# when the same selected IDs and q gate are certified.
# Orientation/sign METADATA is not preserved under this relaxation.
Lffn,delta_z,even_norm,flip,delta_h,delta_x,Thnorm,Txnorm,Tynorm,biasT,errFFN,errH=S.symbols(
    "Lffn delta_z even_norm flip delta_h delta_x Thnorm Txnorm Tynorm biasT errFFN errH",
    nonnegative=True)
chartY=Lffn*delta_z+2*flip*even_norm+errFFN
chartH=Thnorm*delta_h+Txnorm*delta_x+Tynorm*chartY+2*flip*biasT+errH
require("conditional history chart residual transport",
    S.simplify(chartH-(Thnorm*delta_h+Txnorm*delta_x
        +Tynorm*(Lffn*delta_z+2*flip*even_norm+errFFN)
        +2*flip*biasT+errH))==0)
# The ± chart formula cannot silently consume the source's sign=0
# fixed-point case: y=0 and h_next=cap(0)=0 when x=h=0.
require("nonraw zero-sign chart distinct from ± biased maps",
    S.simplify(0*Fchart(0))==0
    and S.simplify(Fchart(0)-(msym*geluf(bsym)+bout))==0)

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
