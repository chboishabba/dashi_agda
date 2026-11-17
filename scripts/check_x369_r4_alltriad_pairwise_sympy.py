#!/usr/bin/env python3
"""All original R4 triads: correlated source pairwise error envelopes.

Pure SymPy/rational model of original R4 score; NO Torch simulation,
hardware rounding receipts, native topk tie verification or Agda kernel.
"""
import sympy as S
R=S.Rational
checks=[]
def check(name,condition):
    if not bool(condition):raise AssertionError("X369_ALLTRIAD_PAIR_FAIL "+name)
    checks.append(name)
def dot(a,b):return sum(i*j for i,j in zip(a,b))
def K(w,x):return (w[0]*x[0]+w[1]*x[2]+w[2]*x[1],
                    w[0]*x[1]+w[1]*x[0]+w[2]*x[2],
                    w[0]*x[2]+w[1]*x[1]+w[2]*x[0])
def q(t):return R(1,2)*sum((t[i]-t[(i+1)%3])**2 for i in range(3))
def qerr(t,e):
    return sum(abs(t[i]-t[(i+1)%3])*(e[i]+e[(i+1)%3])
        +R(1,2)*(e[i]+e[(i+1)%3])**2 for i in range(3))
def gate(x,e,base):
    qs=[q(x[j:j+3]) for j in range(0,len(x),3)]
    Q=[qerr(x[j:j+3],e[j:j+3]) for j in range(0,len(x),3)]
    m=len(qs);avg=sum(qs)/m
    bits=[]
    for j in range(m):
        mid=qs[j]-avg
        radius=((m-1)*Q[j]+sum(Q[k] for k in range(m) if k!=j))/m
        if mid-radius>0:flip=True
        elif mid+radius<=0:flip=False
        else:return None
        bits.append(bool(base[j]) ^ flip)
    return tuple(bits)
def rot(t,bit):return (t[1],t[2],t[0]) if bit else (t[2],t[0],t[1])
def phase(x,bits):
    return tuple(v for j,bit in enumerate(bits)
        for v in rot(x[j*3:j*3+3],bit))
def score(x,h,v,w,b,bit):
    xx=phase(x,bit)
    coeff=tuple(a for j in range(0,len(x),3)
      for a in K(w[j:j+3],xx[j:j+3]))
    return tuple(dot(coeff,he)+dot(v,[abs(z) for z in he])+b[e]
      for e,he in enumerate(h))
def relative_budget(hi,hj,x,v,w,ex,ehi,ehj,ev,ew,ebi,ebj,bits):
    xx=phase(x,bits);ee=phase(ex,bits)
    triple_paths=(((0,0),(1,2),(2,1)),
       ((0,1),(1,0),(2,2)),((0,2),(1,1),(2,0)))
    coeff=[];U=[]
    for j in range(0,len(x),3):
        coeff.extend(K(w[j:j+3],xx[j:j+3]))
        U.extend(sum(abs(w[j+i])*ee[j+k]+
          ew[j+i]*(abs(xx[j+k])+ee[j+k])
          for i,k in path) for path in triple_paths)
    direct=sum(U[l]*abs(hi[l]-hj[l])
        +(abs(coeff[l])+U[l])*(ehi[l]+ehj[l])
        for l in range(len(x)))
    c2=sum(abs(v[l])*(ehi[l]+ehj[l])
        +ev[l]*(abs(abs(hi[l])-abs(hj[l]))
                 +ehi[l]+ehj[l])
        for l in range(len(x)))
    return direct+c2+ebi+ebj
def shift(v,e,s):return tuple(z+s*eps for z,eps in zip(v,e))
x=tuple(map(R,(2,0,0,0,0,0)))
h=[tuple(map(R,z)) for z in ((0,1,0,0,0,0),
   (1,0,1,0,0,0),(0,1,1,0,0,0),(1,1,0,0,0,0))]
v=tuple(map(R,(0,1,1,0,0,0)))
w=tuple(map(R,(2,-1,1,1,0,2)))
bias=tuple(map(R,(0,1,5,10)))
eps=(R(1,256),)*6;eb=R(1,256)
base=(True,False)
for arm,expected in (("coherent",(2,3)),("mixed",(3,2))):
    bits=(True,True) if arm=="coherent" else gate(x,eps,base)
    check(arm+" mixed q gate certification",bits is not None)
    original=score(x,h,v,w,bias,bits)
    ids=sorted(range(4),key=lambda i:(-original[i],i))[:2]
    check(arm+" original ordered top2",tuple(ids)==expected)
    xp=shift(x,eps,+1);wp=shift(w,eps,-1)
    vp=shift(v,eps,+1);hp=[shift(he,eps,-1) for he in h]
    bp=shift(bias,(eb,)*4,+1)
    if arm=="mixed":
        check(arm+" perturbed gate stays admitted",
              gate(xp,eps,base)==bits)
    perturbed=score(xp,hp,vp,wp,bp,bits)
    for i in range(4):
        for j in range(i+1,4):
            B=relative_budget(h[i],h[j],x,v,w,eps,eps,eps,
                              eps,eps,eb,eb,bits)
            check(arm+" exact rational pair interval "+str((i,j)),
               abs((perturbed[i]-perturbed[j])-
                   (original[i]-original[j]))<=B)
            if i in ids and j not in ids:
                check(arm+" strict selected/outside "+str((i,j)),
                      original[i]-original[j]>B)
            if j in ids and i not in ids:
                check(arm+" strict selected/outside "+str((j,i)),
                      original[j]-original[i]>B)
    check(arm+" strict internal slot order",
      original[ids[0]]-original[ids[1]]>
       relative_budget(h[ids[0]],h[ids[1]],x,v,w,
          eps,eps,eps,eps,eps,eb,eb,bits))
    observed=sorted(range(4),key=lambda i:(-perturbed[i],i))[:2]
    check(arm+" perturbed selected order",observed==ids)
    print("R4_ALLTRIAD_PAIR",arm,"source",original,
          "quantized",perturbed,"top2",ids)
print("X369_R4_ALLTRIAD_PAIR_SYMPY_PASS",len(checks),"checks")
