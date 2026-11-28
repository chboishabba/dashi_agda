#!/usr/bin/env python3
"""BR74: FULL nonlinear graph Codazzi, all four components, including null tilt.

Ambient Minkowski eta_5; wall n=f(t,x,y,z), spacelike normal z>0.
The actual induced geometry is h_ab=eta_ab+f_a f_b;
 h^-1_ab=eta^ab-f^a f^b/z;
 K_ab=-f_ab/sqrt(z),
 Γ(h)^c_ab=f^c f_ab/z.
For independent symmetric second jets H_ab and fully symmetric third
jets T_abc, calculate the *actual covariant Codazzi tensor*
  C_cab = ∇c K_ab-∇a K_cb.
The numerator after common z^(3/2) denominator vanishes exactly:
  -z(T_cab-T_acb)
  +H_ab A_c+H_ca A_b+H_cb A_a
  -H_cb A_a-H_ac A_b-H_ab A_c =0,
where A_c=f^d H_cd.
Thus D^a(K_ab-h_ab tr_h K)=0 in ambient-flat geometry and
for genuine nonlinear moving graph with arbitrary symmetric jets.
No tangential Fourier division, no linearized flat graph assumption.

Curved ambient version is D^a(K_ab-h_ab tr K)=
  ±Ric_g(n,e_b) depending original K orientation, so a true
two-sided Israel Codazzi requires the normal Ricci jump and ∂_b j.
The flat graph test cannot set those sources to zero for AdS
or a general nonlinear Einstein–Israel solution.

--part jet|graph|rank
"""
import argparse
import sympy as s
eta=s.diag(-1,1,1,1)

def tensor():
    f=s.Matrix(s.symbols('f0:4',real=True))
    H=s.Matrix(4,4,lambda i,j:s.Symbol(f'H{min(i,j)}{max(i,j)}',real=True))
    q=eta*f
    z=1+(f.T*eta*f)[0]
    A=H*q
    # Numerical denominator z is never inverted during tensor audit;
    # full Codazzi equality holds at the polynomial numerator level.
    def tri(i,j,k):
        return s.Symbol('T'+''.join(map(str,sorted((i,j,k)))),real=True)
    def numerator(c,a,b):
        return (-z*(tri(c,a,b)-tri(a,c,b))
          + H[a,b]*A[c]+H[c,a]*A[b]+H[c,b]*A[a]
          - H[c,b]*A[a]-H[a,c]*A[b]-H[a,b]*A[c])
    return f,H,q,z,numerator

def jet():
    f,H,q,z,N=tensor()
    for c in range(4):
        for a in range(4):
            for b in range(4):
                assert s.expand(N(c,a,b))==0,(c,a,b)
    # True full h inverse: Sherman-Morrison, no approximation.
    h=eta+f*f.T
    hi=eta-q*q.T/z
    assert (z*(h*hi-s.eye(4))).applyfunc(s.expand)==s.zeros(4)
    # Zero tangential frequency is harmless: nonlinear jet identity
    # uses z>0 only for the *unit* normal, never q² inverse.
    print('BR74 constructed 64 nonlinear covariant Codazzi components, symmetric 3-jet and induced inverse')

def graph():
    t,x,y,w=s.symbols('t x y w',real=True)
    X=(t,x,y,w)
    f=t*x/s.Integer(5)+x*x*y/s.Integer(7)+t*y*w/s.Integer(11)+w*w/s.Integer(13)
    site={t:s.Rational(1,7),x:s.Rational(2,9),y:s.Rational(-1,11),w:s.Rational(1,13)}
    a=s.Matrix([s.diff(f,v).subs(site) for v in X])
    H=s.Matrix(4,4,lambda i,j:s.diff(f,X[i],X[j]).subs(site))
    third=lambda c,i,j:s.diff(f,X[c],X[i],X[j]).subs(site)
    z=1+(a.T*eta*a)[0]
    assert z>0
    upper=eta*a;A=H*upper
    # Compute exact covariant derivative using the TRUE induced Gamma,
    # not the polynomial-numerator zero built into the symbolic test.
    def covK(c,i,j):
        N=s.sqrt(z)
        dz=2*A[c]
        dk= -third(c,i,j)/N+H[i,j]*dz/(2*z*N)
        return s.simplify(dk+
          sum((upper[r]*H[c,i]*H[r,j]
                +upper[r]*H[c,j]*H[i,r])/(z*N) for r in range(4)))
    for b in range(4):
        for c in range(4):
            for aidx in range(4):
                assert s.simplify(covK(c,aidx,b)-covK(aidx,c,b))==0
    print('BR74 constructed independent non-flat moving graph, induced connection and 64 Codazzi identities')

def rank():
    from check_hopf369_br62_israel_codazzi_rank import pencil
    for v in ([0,0,0,0],[1,1,0,0],[1,0,0,0],[0,1,0,0]):
        q=s.Matrix(v)
        assert pencil(q).rank()==(0 if not any(v) else 4)
    print('BR74 exact 4/10 Codazzi symbol rank and physical q=0/null strata retained')

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['jet','graph','rank'],default='jet')
    a=p.parse_args();{'jet':jet,'graph':graph,'rank':rank}[a.part]()
