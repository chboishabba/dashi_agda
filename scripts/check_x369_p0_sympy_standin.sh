#!/usr/bin/env bash
# SymPy is a bounded symbolic CI stand-in; it is NOT an Agda kernel check.
set -euo pipefail
python3 - <<'PY'
import itertools
import sympy as sp

checks=[]
def check(name, assertion):
    if not assertion:
        raise AssertionError('X369_SYMPY_STANDIN_FAIL: '+name)
    checks.append(name)

a,b,c,A,B,C = sp.symbols('a b c A B C', integer=True)
s,f,r = a*A+b*B+c*C, a*B+b*C+c*A, a*C+b*A+c*B
q=lambda x,y,z:x*x+y*y+z*z-x*y-y*z-z*x
D=(a+b+c)*(A+B+C)
check('original directed triple total = DC(x) DC(h)', sp.expand(s+f+r-D)==0)
check('original directed 3->2+DC decoder', sp.expand((D-s-f)-r)==0)
check('original directed 2+DC source reconstruction', sp.expand(((D-s)-f)-r)==0)
check('original 2q(x)q(h) factorization', sp.expand((r-s)**2+(s-f)**2+(f-r)**2-2*q(a,b,c)*q(A,B,C))==0)
check('C3 source displacement = 2q(x)', sp.expand((b-a)**2+(c-b)**2+(a-c)**2-2*q(a,b,c))==0)
check('q centered projection identity', sp.expand(q(a,b,c)-sp.Rational(3,2)*((2*a-b-c)**2/6+(b-c)**2/2))==0)

ws,wf,wr = sp.symbols('w_s w_f w_r')
score=ws*s+wf*f+wr*r
reduced=(ws-wr)*s+(wf-wr)*f+wr*D
check('arbitrary learned head score 3->2+DC', sp.expand(score-reduced)==0)
check('x-centered exact two-channel score', sp.expand((score-(ws-wr)*s-(wf-wr)*f).subs(c,-a-b))==0)
check('h-centered exact two-channel score', sp.expand((score-(ws-wr)*s-(wf-wr)*f).subs(C,-A-B))==0)
check('original source collision at two channels', (s.subs({a:1,b:0,c:0,A:0,B:0,C:0}),f.subs({a:1,b:0,c:0,A:0,B:0,C:0}),r.subs({a:1,b:0,c:0,A:0,B:0,C:0}))==(0,0,0) and (s.subs({a:1,b:0,c:0,A:0,B:0,C:1}),f.subs({a:1,b:0,c:0,A:0,B:0,C:1}),r.subs({a:1,b:0,c:0,A:0,B:0,C:1}))==(0,0,1))
check('original source surjectivity onto directed triples', all(sp.expand(z.subs({a:1,b:0,c:0})-t)==0 for z,t in zip([s,f,r],[A,B,C])))

P=sp.Matrix([[0,0,1],[1,0,0],[0,1,0]])
t=sp.Matrix([s,f,r]); w=sp.Matrix([ws,wf,wr])
rotated=sp.Matrix([s,f,r]).subs({a:b,b:c,c:a}, simultaneous=True)
check('directed channel C3 permutation from original x', all(sp.expand(u-v)==0 for u,v in zip(rotated,P*t)))
check('C3 permutes back after three rotations',P**3==sp.eye(3))
check('unrestricted head gauge transport',sp.expand((w.T*(P*t)-(P.T*w).T*t)[0])==0)
M2=sp.Matrix([[-1,-1],[1,0]])
check('centered two-channel C3 is order three',M2**3==sp.eye(2))
centered_h={C:-A-B}
check('original centered source action intertwines two-channel C3',
    all(sp.expand(z.subs(centered_h))==0 for z in list(
        sp.Matrix([r,s])-M2*sp.Matrix([s,f]))))

# Finite carrier exhaustive control: two independent tags per phase.
inputs=list(itertools.product(range(3),[False,True]))
for enc in itertools.product([False,True],repeat=len(inputs)):
    table=dict(zip(inputs,enc))
    pairs_ok=all(table[x]!=table[y] or x[0]==y[0]
                 for x,y in itertools.combinations(inputs,2))
    if pairs_ok:
        raise AssertionError('one-bit finite consumer collision counterexample')
check('all 64 one-bit encoders fail consumer sufficiency',True)
encode=lambda state:((state[0]>>1)&1,state[0]&1)
check('2-bit phase code sufficiency',all(encode(x)!=encode(y) or x[0]==y[0] for x,y in itertools.product(inputs,repeat=2)))
check('two-tag source collision under phase code',encode((1,False))==encode((1,True)))
check('phase action commutes with 2-bit code',all(encode(((p+1)%3,t))==encode(((p+1)%3,False)) for p,t in inputs))

step=lambda state:((state[0]+(1 if state[1] else 0))%3,state[1])
check('present phase code cannot retain tag-sensitive next phase',encode((0,False))==encode((0,True)) and encode(step((0,False)))!=encode(step((0,True))))
step_simple=lambda state:((state[0]+1)%3,state[1])
step_code=lambda bits:encode(((2*bits[0]+bits[1]+1)%3,False))
for n in range(10):
    for state in inputs:
        fine=state; coded=encode(state)
        for _ in range(n):
            fine=step_simple(fine); coded=step_code(coded)
        if encode(fine)!=coded:
            raise AssertionError('future quotient step '+str(n)+' '+str(state))
check('all 60 finite futures commute with encoded transition',True)

pairs=list(itertools.product(range(3),repeat=2))
y=lambda pair:sum(pair)%3
R=lambda pair:((pair[0]+1)%3,pair[1])
check('mod3 task action commutation',all(y(R(p))==(y(p)+1)%3 for p in pairs))
memorizer={pair:y(pair) for pair in pairs}; memorizer[(2,2)]=0
n_def=lambda rule:sum(rule[R(pair)]!=(rule[pair]+1)%3 for pair in pairs)
check('algorithmic equivariance defect zero',n_def({p:y(p) for p in pairs})==0)
check('memorizer equivariance defect two',n_def(memorizer)==2)
check('heldout nonidentification',all(memorizer[p]==y(p) for p in pairs if p!=(2,2)) and memorizer[(2,2)]!=y((2,2)))

# Exact source-weighted error propagation under independently bounded
# scalar quantization residuals; this is NOT a verified quantizer bound.
total,ss,ff,eD,es,ef=sp.symbols('total ss ff eD es ef')
packed=lambda tt,si,fi:(ws-wr)*si+(wf-wr)*fi+wr*tt
quant_delta=packed(total+eD,ss+es,ff+ef)-packed(total,ss,ff)
check('original weighted score quantization error identity',
      sp.expand(quant_delta-((ws-wr)*es+(wf-wr)*ef+wr*eD))==0)
centerA={a:1,b:0,c:0,A:0,B:0,C:0}
centerB={a:1,b:0,c:0,A:0,B:1,C:-1}
check('centered source counterexample to first channel',
    all(sp.expand(D.subs(z))==0 for z in [centerA,centerB])
    and sp.expand(s.subs(centerA)-s.subs(centerB))==0
    and sp.expand(r.subs(centerA)-r.subs(centerB))!=0
    and sp.expand(f.subs(centerA)-f.subs(centerB))!=0)
check('declared original-coordinate MDL minimal sufficient candidate is 2',
    min(cost for name,cost,sufficient in
        [('first',1,False),('two-centered',2,True),('raw',3,True)]
        if sufficient)==2)
# A shared learned head means a common expert DC is a common
# additive logit offset. It cancels even if that DC is nonzero.
si,fi,ri,sj,fj,rj=sp.symbols('si fi ri sj fj rj')
Di=si+fi+ri; Dj=sj+fj+rj
source_difference=(ws*si+wf*fi+wr*ri)-(ws*sj+wf*fj+wr*rj)
two_difference=(ws-wr)*(si-sj)+(wf-wr)*(fi-fj)
check('original common-DC expert score difference factors through two',
    sp.expand(source_difference-two_difference-wr*(Di-Dj))==0)
check('nonzero common-DC exact two-channel relative score',
    sp.expand((source_difference-two_difference).subs(rj,Di-sj-fj))==0)
check('different-DC source feature collision can change relative score',
    sp.expand((source_difference-two_difference).subs({
        si:0,fi:0,ri:1,sj:0,fj:0,rj:0,ws:1,wf:1,wr:1}))==1)
check('centered shared activation zeroes every expert DC',
    sp.expand(D.subs(c,-a-b))==0)
history_alt=sp.symbols('H_alt0 H_alt1 H_alt2')
check('source activation centering ensures equal DC across histories',
    sp.expand(((a+b+c)*(A+B+C)-(a+b+c)*sum(history_alt)).subs(c,-a-b))==0)
check('non-centered activation can retain unequal expert DC',
    sp.expand(((a+b+c)*(A+B+C)-(a+b+c)*sum(history_alt)).subs({
        a:1,b:0,c:0,A:0,B:0,C:1,
        history_alt[0]:0,history_alt[1]:0,history_alt[2]:0}))==1)


# Exact source-head quantization safety needs BOTH a bound and a
# strict selected-vs-unselected margin. This is finite stand-in for
# the Agda interval certificate, not a source quantizer validation.
positive=0
for si,sj,ei,ej in itertools.product(range(-2,4), repeat=4):
    if si <= sj:
        continue
    bound_i=abs(ei); bound_j=abs(ej)
    if si-bound_i>sj+bound_j:
        positive+=1
        if not si+ei>sj+ej:
            raise AssertionError('quantized strict 2-expert margin failed')
check('all 2-expert strict error-envelopes preserve order',positive>0)
# Demonstrate strict separation is sufficient but not necessary:
# conservative bounds can overlap with zero actual perturbation.
check('strict margin not necessary',not (1-2>0+2) and (1+0>0+0))
# For THREE experts, every source top-1 is preserved whenever
# its lower envelope outranks every competitor's upper envelope.
certified=0
for scores in itertools.product((0,1,3),repeat=3):
    winner=max(range(3),key=lambda i:scores[i])
    if any(scores[winner]<=scores[j] for j in range(3) if j!=winner):
        continue
    for errors in itertools.product((-1,0,1),repeat=3):
        if all(scores[winner]-abs(errors[winner])>
               scores[j]+abs(errors[j])
               for j in range(3) if j!=winner):
            certified+=1
            if max(range(3),key=lambda i:scores[i]+errors[i])!=winner:
                raise AssertionError('quantized 3-expert top1 changed')
check('all certified 3-expert top1 sets preserved',certified>0)
# Exact two-channel quantizer-score error also obeys the absolute
# coefficient envelope (triangle inequality). Quantizers themselves
# must provide actual error tolerances.
for W in itertools.product((-2,-1,0,1,2),repeat=3):
    w0,w1,w2=W
    for residuals in itertools.product((-1,0,1),repeat=3):
        ds,df,dD=residuals
        err=(w0-w2)*ds+(w1-w2)*df+w2*dD
        budget=abs(w0-w2)*abs(ds)+abs(w1-w2)*abs(df)+abs(w2)*abs(dD)
        if abs(err)>budget:
            raise AssertionError('quantized error exceeds triangle envelope')
check('source coefficient-weighted quantizer error envelope',True)
print('X369_SYMPY_STANDIN_PASS',len(checks),'symbolic/finite checks')
PY
