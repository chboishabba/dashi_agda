"""Backward weld of existing #1530 fixed-flux and signed inverse owners.
Exact symbolic composition, not a material calibration or Einstein solution.
"""
import sympy as s

def check():
    x,B,g,D,a,j,k,H,K,t=s.symbols("x B gamma Delta alpha j k H K target", real=True, nonzero=True)
    V=D*x**2/2+g*x**4/4-B*x
    G=s.Matrix([[K,-K*a*x],[-K*a*x,H+K*a*a*x*x]])
    flux=s.Matrix([j,k])
    R=V-(flux.T*G.inv()*flux)[0]/2
    Be=B+a*j*k/H
    De=D-a*a*j*j/H
    assert s.simplify(R-(De*x*x/2+g*x**4/4-Be*x-j*j/(2*K)-k*k/(2*H)))==0
    inverse=Be/t-g*t*t+a*a*j*j/H
    assert s.simplify(s.diff(R,x).subs({x:t,D:inverse}, simultaneous=True))==0
    assert s.simplify(s.diff(R,x,2).subs({x:t,D:inverse}, simultaneous=True)-(Be/t+2*g*t*t))==0
    for target in (-1,1):
        fixture={B:0,g:1,a:1,j:1,k:s.Rational(1,10),H:1,K:1,t:target}
        bare=s.simplify(inverse.subs(fixture))
        curvature=s.simplify((Be/t+2*g*t*t).subs(fixture))
        assert curvature>0
        assert bare==s.Rational(target,10)
        print(target, "bare stiffness",bare,"relaxed curvature",curvature)
    # Backward elimination of the existing material P port's stable Hessian.
    C,L,Z=s.symbols("C L Z", positive=True)
    M=s.Matrix([[Z,L],[L,C]])
    assert s.simplify(M.det()/C-(Z-L*L/C))==0
    print("PASS fixed-flux signed inverse and material Schur weld")
if __name__=="__main__":
    check()
