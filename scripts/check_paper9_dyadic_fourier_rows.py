import sympy as s
q,n,x,y,h,z=s.symbols('q n x y h z')
cs={3:[[0,1,4,1],[0,3,0,-3],[0,3,-6,3],[1,-3,3,-1]],5:[[0,1,26,66,26,1],[0,5,50,0,-50,-5],[0,10,20,-60,20,10],[0,10,-20,0,20,-10],[0,5,-20,30,-20,5],[1,-5,10,-10,5,-1]]}
X=lambda t:t/(1-t)**2
P={4:lambda t:t+6*t**2,6:lambda t:t+30*t**2+120*t**3}
checks=0
def eq(a,b):
    global checks
    assert s.cancel(a-b)==0,(a,b)
    checks+=1
for k,c in cs.items():
    B=sum(n**i*sum(a*q**j for j,a in enumerate(row)) for i,row in enumerate(c))
    eq(B-q*B.subs(n,n+1),n**k*(1-q)**(k+1))
    eq(q*B.subs(n,1)/(1-q)**(k+1),P[k+1](X(q)))
    for N in range(1,9):
        eq((1-q)**(k+1)*sum(j**k*q**j for j in range(1,N+1)),q*B.subs(n,1)-q**(N+1)*B.subs(n,N+1))
eq(X(q)+X(-q),4*X(q*q))
eq(X(q)*X(-q),-X(q*q))
for k,p in P.items():
    eq(p(X(q))+p(X(-q)),2**k*p(X(q*q)))
    eq(p(X(s.Integer(-1))),s.Rational(1,8) if k==4 else -s.Rational(1,4))
    for N in (2,4,8):
        # Signed dyadic refinement: use exact roots of unity symbolically by recursion.
        expr=p(X(q))
        for j in range(N.bit_length()-1):
            eq(expr+p(X(-q)),2**k*p(X(q*q)))
for N in range(2,17):
    eq(sum((h*z)**j/s.factorial(j) for j in range(N)),1+h*z+h*h*sum(h**j*z**(j+2)/s.factorial(j+2) for j in range(N-2)))
print(f'{checks} exact symbolic identities passed (not Agda kernel validation)')
