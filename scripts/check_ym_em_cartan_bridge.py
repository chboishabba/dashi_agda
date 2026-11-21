"""Exact U(1) Cartan restriction inside SU(2) curvature and finite gap warning.

Shared exterior derivative/Hodge objects are legitimate reusable interfaces.
An abelian reduction is not a proof of the interacting 4D YM mass gap.
"""
import sympy as s

def main():
    x,y,g=s.symbols('x y g',real=True)
    a,b,c,d=s.symbols('a b c d',real=True)
    # Anti-Hermitian su(2) generators T_i = -i sigma_i / 2.
    I=s.I
    sx=s.Matrix([[0,1],[1,0]])
    sy=s.Matrix([[0,-I],[I,0]])
    sz=s.Matrix([[1,0],[0,-1]])
    T=[-I*S/2 for S in (sx,sy,sz)]
    checks=0
    for i,j,k,sign in ((0,1,2,1),(1,2,0,1),(2,0,1,1)):
        assert T[i]*T[j]-T[j]*T[i]==T[k]
        checks+=1
    # Curvature F_xy = d_x A_y - d_y A_x + g[A_x,A_y].
    A_x=a*x*T[2]; A_y=b*y*T[2]
    F=s.diff(A_y,x)-s.diff(A_x,y)+g*(A_x*A_y-A_y*A_x)
    assert F==s.zeros(2)
    checks+=1
    A_x=c*y*T[2]; A_y=d*x*T[2]
    F=s.simplify(s.diff(A_y,x)-s.diff(A_x,y)+g*(A_x*A_y-A_y*A_x))
    assert s.simplify(F-(d-c)*T[2])==s.zeros(2)
    checks+=1
    # Same derivative-free fields: nonabelian interactions remain.
    A_x=a*T[0]; A_y=b*T[1]
    F=s.simplify(g*(A_x*A_y-A_y*A_x))
    assert s.simplify(F-g*a*b*T[2])==s.zeros(2) and F!=s.zeros(2)
    checks+=1
    # Exact quadratic gauge action density differs by interaction.
    norm=lambda M:s.simplify(-2*s.trace(M*M))
    assert s.factor(norm(F))==g*g*a*a*b*b
    checks+=1
    # Free massless U(1) Fourier dispersion has no strictly positive gap.
    k,m=s.symbols('k m',real=True,positive=True)
    assert s.limit(s.sqrt(k*k),k,0,dir='+')==0
    assert s.limit(s.sqrt(k*k+m*m),k,0,dir='+')==m
    checks+=2
    # Finite periodic lattice spectral gap alone is a finite size effect.
    L=s.Matrix([[2,-1,0,-1],[-1,2,-1,0],[0,-1,2,-1],[-1,0,-1,2]])
    assert L.eigenvals()=={s.S(0):1,s.S(2):2,s.S(4):1}
    checks+=1
    # As lattice size/extent grows, first positive free eigenvalue -> 0.
    N=s.symbols('N',positive=True)
    assert s.limit(4*s.sin(s.pi/N)**2,N,s.oo)==0
    checks+=1
    print(f'{checks}/{checks} PASS local SymPy {s.__version__}; shared exterior/Hodge bridge, strict U1 vs SU2 obstruction')
if __name__=='__main__':main()
