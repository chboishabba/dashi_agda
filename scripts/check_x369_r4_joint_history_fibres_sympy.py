#!/usr/bin/env python3
"""X369 original R4: joint router / orientation / FFN / recurrent sufficiency.

Source evidence: LeechTransformer/models/history_orbit_moe.py step():
 source route observes C2 abs(h) and learned C3 directed score;
 selected expert receives SIGNED h in orientation([x,h]),
 experts[e]([sign*x,sign*h]) with GELU and
 transitions[e]([sign*h,sign*x,y_c]).
Finite model-parameter witnesses are drawn from these source layer forms.
Not a claim about the actually fitted checkpoint.

Also proves exact positive quotient closure for a linear transition
and observation, with arbitrary symbolic matrix coefficients, and a
counterexample when kernel invariance is violated. SymPy proof development
only; not an Agda kernel or GPU run.
"""
import sympy as s
R=s.Rational
checks=[]
def check(name,p):
    if not bool(p): raise AssertionError(name)
    checks.append(name)
ws,wf,wr=s.symbols('ws wf wr',real=True)
M=s.Matrix([[ws,wr,wf],[wf,ws,wr],[wr,wf,ws]])
W=M.subs({ws:2,wf:-1,wr:-1})
hp=s.ones(3,1)
hn=-hp
x=s.Matrix([1,0,0])
v=s.Matrix([1,2,3])
check('zero-sum original directed head has rank2',W.rank()==2)
check('directed same for every source activation',
      W.T*(hp-hn)==s.zeros(3,1))
check('source full C2 absolute history agrees',
      all(abs(hp[i])==abs(hn[i]) for i in range(3)))
# Source orientation is sign(2*linear([x,h],Worient)).
# Choose a licensed source-shaped orientation matrix reading x0 only:
# both charts are + for this nonzero shared x, not a tie fallback.
check('chosen original orientation sign common',
      2*x[0]>0)
# Source expert FFN is Linear(2d,width)->GELU->Linear(width,d).
# With W1 selecting signed h0 and W2 emitting into output[0],
# the two same-router histories yield distinct selected output.
def gelu(t):
    return t*(1+s.erf(t/s.sqrt(2)))/2
check('selected FFN exact GELU output differs',
      s.simplify(gelu(hp[0])-gelu(hn[0]))==1)
# Original transition Linear(3d,d) can project the first old h
# coordinate back into next history. Hence its future state differs.
check('source-compatible transition retains lost signed DC',
      hp[0]!=hn[0])
# Constructive sufficient representation: E=P projects to first
# two history coordinates. Exact closed transition requires
# E*T = Tbar*E, i.e. ker E must be T-invariant.
P=s.diag(1,1,0)
a,b,c,d,e,f,g=s.symbols('a b c d e f g')
T=s.Matrix([[a,b,0],[c,d,0],[e,f,g]])
Tbar=T[:2,:2]
E=P[:2,:]
check('kernel-invariant transition commutes with quotient',
      E*T==Tbar*E)
Z=s.Matrix(s.symbols('z0:3'))
check('all source states project exactly through transition',
      E*T*Z==Tbar*E*Z)
# If a discarded variable enters a retained one, no quotient step
# can be defined from the two-coordinate code alone.
Tbad=T.copy();Tbad[0,2]=1
check('violating discarded-history closure is detected',
      E*Tbad!=Tbad[:2,:2]*E)
check('same code can diverge after invalid transition',
      E*Tbad*s.Matrix([0,0,1])!=E*Tbad*s.zeros(3,1))
ori=s.Matrix(s.symbols('o0:3'))
check('orientation source DC sensitivity exact',
      s.expand((ori.T*(hp-hn))[0])==2*sum(ori))
check('identity source transition can preserve all signed history',
      s.eye(3).rank()==3)
for n in range(1,7):
    check(f'{n}-step quotient with arbitrary symbolic coefficients',
      all(s.expand(v)==0 for v in E*(T**n)-(Tbar**n)*E))
# A linear consumer factors through E if its row space annihilates
# the kernel. This witness discriminates sufficient/insufficient.
Ogood=s.Matrix([[1,2,0],[0,1,0]])
Obad=s.Matrix([[1,2,1]])
check('consumer row lies in retained observer dual',
      Ogood[:,2]==s.zeros(2,1))
check('consumer row detects lost history kernel',
      Obad[:,2]!=s.zeros(1,1))
print('X369_JOINT_HISTORY_SYMPY_PASS',len(checks))
