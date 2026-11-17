#!/usr/bin/env python3
"""Source R4 pairwise correlated score-interval proof development (SymPy).

Use ONLY after fixing the original coherent/mixed q branch. Precision/error
bounds here are rational fixtures, not original Leech hardware receipts.
"""
import sympy as S
R=S.Rational
tests=[]
def check(label,ok):
    if not bool(ok):raise AssertionError("X369_PAIRWISE_FAIL: "+label)
    tests.append(label)
def K(w,x):
    return (w[0]*x[0]+w[1]*x[2]+w[2]*x[1],
            w[0]*x[1]+w[1]*x[0]+w[2]*x[2],
            w[0]*x[2]+w[1]*x[1]+w[2]*x[0])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
add=lambda a,b:tuple(x+y for x,y in zip(a,b))
sub=lambda a,b:tuple(x-y for x,y in zip(a,b))

a,b,c=S.symbols("a b c")
A,B,C,D,E,F=S.symbols("A B C D E F")
ws,wf,wr=S.symbols("ws wf wr")
dx=S.symbols("dx0:3");dw=S.symbols("dw0:3")
dhi=S.symbols("dhi0:3");dhj=S.symbols("dhj0:3")
x=(a,b,c);w=(ws,wf,wr);hi=(A,B,C);hj=(D,E,F)
u=K(w,x);du=sub(K(add(w,dw),add(x,dx)),u)
H=sub(hi,hj);dH=sub(dhi,dhj)
pair_orig=dot(u,H)
pair_quant=dot(K(add(w,dw),add(x,dx)),
               sub(add(hi,dhi),add(hj,dhj)))
check("exact fused pairwise perturbation identity",
 S.expand(pair_quant-pair_orig
          -(dot(du,H)+dot(u,dH)+dot(du,dH)))==0)
check("common source/head perturbation cannot distinguish equal histories",
 S.expand(dot(du,sub(hi,hi)))==0)

def kernel_budget(w,x,ew,ex):
    triples=(((0,0),(1,2),(2,1)),
             ((0,1),(1,0),(2,2)),
             ((0,2),(1,1),(2,0)))
    return tuple(sum(abs(w[i])*ex[j]+
                     ew[i]*(abs(x[j])+ex[j]) for i,j in path)
                 for path in triples)
def pair_budget(hi,hj,w,x,v,ew,ex,ev,eh,eb):
    u=K(w,x);U=kernel_budget(w,x,ew,ex)
    directed=sum(U[i]*abs(hi[i]-hj[i])
       +(abs(u[i])+U[i])*(eh[i]+eh[i]) for i in range(3))
    c2=sum(abs(v[i])*(eh[i]+eh[i])
       +ev[i]*(abs(abs(hi[i])-abs(hj[i]))+eh[i]+eh[i])
       for i in range(3))
    return directed+c2+2*eb

# SOURCE coherent first-triad fixture; x has ALREADY been rotated +120
# from original activation (2,0,0) to phase input (0,0,2).
x=(R(0),R(0),R(2))
w=(R(2),R(-1),R(1));v=(R(0),R(1),R(1))
h=[tuple(map(R,z)) for z in
   ((0,1,0),(1,0,1),(0,1,1),(1,1,0))]
bias=(R(0),R(1),R(5),R(10))
ex=eh=ew=ev=(R(1,256),)*3
eb=R(1,256)
score=lambda he,ww=w,xx=x,vv=v:dot(K(ww,xx),he)+dot(vv,[abs(z) for z in he])
source=[score(he)+bias[i] for i,he in enumerate(h)]
rank=sorted(range(4),key=lambda i:(-source[i],i))
check("coherent source ordered top2",(rank[:2])==[2,3])
for i in (2,3):
    for j in (0,1):
        check("selected/unselected pair "+str((i,j)),
              source[i]-source[j]>
              pair_budget(h[i],h[j],w,x,v,ew,ex,ev,eh,eb))
check("internal selected slot pair",
      source[2]-source[3]>
      pair_budget(h[2],h[3],w,x,v,ew,ex,ev,eh,eb))
sign=(1,-1,1)
xx=tuple(z+s*e for z,s,e in zip(x,sign,ex))
ww=tuple(z-s*e for z,s,e in zip(w,sign,ew))
vv=tuple(z+s*e for z,s,e in zip(v,sign,ev))
hnew=[tuple(z-eh[i] for i,z in enumerate(he)) for he in h]
qscore=[score(he,ww,xx,vv)+bias[i]+eb for i,he in enumerate(hnew)]
for i in range(4):
    for j in range(i+1,4):
        check("source rational pair interval "+str((i,j)),
          abs((qscore[i]-qscore[j])-(source[i]-source[j]))
          <=pair_budget(h[i],h[j],w,x,v,ew,ex,ev,eh,eb))
Q=S.symbols("Q0:3",nonnegative=True)
for m in (2,3):
    for i in range(m):
        old=Q[i]+sum(Q[:m])/m
        sharp=((m-1)*Q[i]+sum(Q[k] for k in range(m) if k!=i))/m
        check("q mean correlation "+str((m,i)),
              S.simplify(old-sharp)==2*Q[i]/m)
print("X369_R4_PAIRWISE_SYMPY_PASS",len(tests),"checks")
