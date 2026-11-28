"""Exact stationary chain bound on original eight-step same-clock forcing."""
import sympy as S
from solar_reciprocal_unfrozen_weld import exact

def certify():
    a,b,l,w=S.symbols('a b l w',positive=True)
    B=S.Matrix([[1,-1,0],[0,1,-1]]);Z=(1-w*w)*S.eye(3)+B.T*S.diag(a,b)*B+S.I*w*S.diag(1+l,1,1)
    norm=lambda z:S.expand(z*S.conjugate(z))
    low=2*(S.sqrt(2)-1);high=2*(S.sqrt(2)+1)
    # The two positive-frequency Fourier bins carry these total squared forces.
    f=S.Matrix([1,1,0,0,-1,-1,0,0]);weights=[]
    for j in (1,3):
        F=S.expand_complex(sum(f[k]*S.exp(-S.I*S.pi*j*k/4) for k in range(8))/8)
        weights.append(S.simplify(16*norm(F)))
    assert weights==[2+S.sqrt(2),2-S.sqrt(2)] and sum(weights)==4
    # Solve the frequency-domain chain by its first two rows. All reciprocal
    # coupling powers have nonnegative coefficients at low frequency.
    det=Z.det();assert S.simplify(Z.inv()[0,2]-a*b/det)==0
    Z0,Z1=Z[0,0],Z[1,1]
    def cap(expr):
        p=S.Poly(S.expand(expr.subs({a:1/a,b:1/b})),a,b,l)
        assert all(S.simplify(v.subs(w,low))>=0 for v in p.coeffs())
        A,B,C=S.Poly(S.simplify(p.as_expr().subs({a:1,b:1,w:low})),l).all_coeffs()
        assert A>0 and B>0 and C>0
        return 1/(B+2*S.sqrt(A*C))
    low_output=weights[0]*low**2*cap(norm(det)/(a*a*b*b))
    low_eff=cap(1+l+norm(Z0)/a**2+norm(Z1*Z0-a*a)/(a*a*b*b))
    # At high frequency |v1/v0|² >= w²(1+l)²/a² >= w²(1+l)².
    # Thus efficiency <= 1/(4w²), and source work <= squared forcing by
    # N=sum damping*v² >= sum v² and Cauchy. Zero coupling yields zero load.
    high_eff=1/(4*high**2);high_output=weights[1]*high_eff
    assert high_eff<low_eff<S.Rational(35,1000)
    assert low_output+high_output<S.Rational(59,1000)
    f=[1,1,0,0,-1,-1,0,0];rows=[[5,544],[394,744],[962,410],[949,69],[738,52],[185,974],[799,904]]
    z=[S.Matrix(r)/1000 for r in rows];z.append(sum(((-1)**k*v for k,v in enumerate(z)),S.zeros(2,1)))
    r=exact(z,f,eta=S.Rational(9,20))
    assert r['output']>S.Rational(59,1000) and r['output']/r['natural']>S.Rational(35,1000)
    print('PASS all stationary chain couplings and loads', 'low_output',float(low_output),'high_output_bound',float(high_output),'total_bound',float(low_output+high_output),'efficiency_bound',float(low_eff),'witness_output',float(r['output']),'witness_efficiency',float(r['output']/r['natural']))
    print('sufficient reverse recovery',float((low_eff*r['natural']-r['receiver']+r['buy'])/r['sell']))
if __name__=='__main__':certify()
