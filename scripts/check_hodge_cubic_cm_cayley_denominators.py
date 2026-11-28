"""Actual cubic CM seed: local small Cayley rotations, unbounded denominators,
and invariant full signed orientation. No generic algebraicity claim."""
import sympy as s

t = s.symbols('t')
f=t**3+t**2-2*t-1
pi=2-t
D=130001
p=29
checks=0

def ck(ok):
    global checks
    if not ok: raise AssertionError('Cayley orbit guard failed')
    checks+=1

def red(a):
    num,den=s.fraction(s.cancel(a))
    return s.rem(s.rem(num,f,t)*s.invert(den,f,t),f,t).expand()

def mr(A): return A.applyfunc(red)

def pf(A):
    if not A.rows:return s.Integer(1)
    return red(sum((-1)**(j+1)*A[0,j]*pf(A.extract([i for i in range(1,A.rows) if i!=j],[i for i in range(1,A.rows) if i!=j])) for j in range(1,A.rows)))

Q=s.diag(t,t*pi,-1,-pi,-1,-pi)
E=s.Matrix([[0,-1,-4,0,4,-6],[1,0,-5,2,-5,-1],[4,5,0,3,-6,2],[0,-2,-3,0,-3,-6],[-4,5,6,3,0,-5],[6,1,-2,6,5,0]])
S=s.zeros(6)
for i,u in enumerate([t,-1,-1]):
    S[2*i,2*i+1]=-(i+1)*u*pi
    S[2*i+1,2*i]=-S[2*i,2*i+1]
S=D*S+E
A=mr(Q.inv()*S/D)
ck(mr(A.T*Q+Q*A)==s.zeros(6))
# The (1,3) entry of gAg^-1, with 1-based matrix labels.
n=s.symbols('n')
num=s.expand(-4*(n*n-pi)+10*n)
# Local prime theta=3 mod 29, n=1 mod 29.
ck(int(f.subs(t,3))%p==0)
ck(int(s.diff(f,t).subs(t,3))%p!=0)
ck((1+2-3)%p==0)
ck((int(num.subs({t:3,n:1})))%p==2)
ck(D%p!=0)
ck(3%p!=0)
# Hensel-lift theta and n using the same selected prime; force exactly
# valuation k by choosing n at the next digit different from the root.
th=3; root=1
for k in range(1,9):
    mod=p**k; nxt=p*mod
    ths=[th+j*mod for j in range(p) if int(f.subs(t,th+j*mod))%nxt==0]
    ck(len(ths)==1); th=ths[0]
    roots=[root+j*mod for j in range(p) if ((root+j*mod)**2+2-th)%nxt==0]
    ck(len(roots)==1)
    chosen=(roots[0]+mod)%nxt + nxt
    v=chosen*chosen+2-th
    ck(v%mod==0 and v%nxt!=0)
    ck(chosen%p==1 and (int(num.subs({t:th,n:chosen})))%p==2)
    ck(chosen>=nxt)
    root=roots[0]
    print('exact negative valuation',-k,'integer parameter',chosen)
# Field-level orthogonality and invariant Pfaffian on selected actual
# rotations. The general identity follows from the determinant formula.
for j in (1,30,842):
    g=s.eye(6); inv=s.eye(6)
    g[:2,:2]=s.Matrix([[j*j-pi,-2*j*pi],[2*j,j*j-pi]])/(j*j+pi)
    inv[:2,:2]=s.Matrix([[j*j-pi,2*j*pi],[-2*j,j*j-pi]])/(j*j+pi)
    g=mr(g);inv=mr(inv)
    ck(mr(g*inv)==s.eye(6));ck(mr(g.T*Q*g-Q)==s.zeros(6));ck(red(g.det())==1)
    C=mr(g*A*inv); M=mr(D*Q*C)
    ck(mr(M.T+M)==s.zeros(6));ck(pf(M)==pf(S))
    ck(red(C[0,2]-num.subs(n,j)/(D*t*(j*j+pi)))==0)
print(f'{checks}/{checks} exact Cayley orbit guards PASS')
