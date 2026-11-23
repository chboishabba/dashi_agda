import sympy as s

def run():
    e0,e1,h0,h1,p0,p1,a0,a1,b,eta,dt,eps,mu,k,j=s.symbols('e0 e1 h0 h1 p0 p1 a0 a1 beta eta dt eps mu k j', real=True)
    E=(e0+e1)/2; H=(h0+h1)/2; dp=p1-p0
    G=(a0+a1)*(p0+p1)/4+b*(p0+p1)*(p0*p0+p1*p1)/4
    U=lambda e,h,p,a:(eps*e*e+mu*h*h+a*p*p)/2+b*p**4/4
    rE=eps*(e1-e0)+dp-dt*(k*H+j)
    rH=mu*(h1-h0)+dt*k*E
    rP=eta*dp/dt+G-E
    mod=(a1-a0)*(p0*p0+p1*p1)/4
    ledger=U(e1,h1,p1,a1)-U(e0,h0,p0,a0)-dt*E*j-mod+eta*dp*dp/dt
    checks=[s.expand(ledger-E*rE-H*rH-dp*rP)==0]
    # Two finite rectangular apertures, ideal multiplicative observation.
    w,T,tau=s.symbols('w T tau', real=True, nonzero=True)
    A=2*s.sin(w*T/2)/w
    F=A*(1+s.exp(-s.I*w*tau))
    checks.append(s.simplify(s.expand_complex(F*s.conjugate(F))-A*A*(2+2*s.cos(w*tau)))==0)
    checks.append(s.limit(A,w,0)==T)
    checks.append(s.simplify(F.subs(tau,0)-2*A)==0)
    # Fixed causal finite state-map fixture, separate from nonlinear material.
    M=s.Matrix([[1,1],[0,1]]); B=s.Matrix([0,1]); C=s.Matrix([[1,0]])
    green=lambda i,j: s.zeros(1,1) if i<=j else C*M**(i-j-1)*B
    checks += [green(0,0)==s.zeros(1,1),green(1,0)==s.zeros(1,1),green(2,0)==s.Matrix([[1]]),green(3,1)==green(2,0)]
    assert all(checks),checks
    print(f'{len(checks)}/{len(checks)} PASS; SymPy {s.__version__}')
if __name__=='__main__':run()
