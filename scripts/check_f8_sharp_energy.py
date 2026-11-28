"""Original moving-wall energy spectrum; signed forward/reverse norm bounds."""
import json
from fractions import Fraction as Q
from check_f8_local_dual_weld import I


def rate(box,reverse=False):
    """Upper norm growth rate on all y>=0 via convexity in b/(b+y)."""
    b=I(*box[0]);beta=(1+b*b).sqrt();a=b/(beta**4);v=-b/beta
    if reverse:v=-v
    vals=[]
    for x in (0,1):
        c=3*v*x/(2*b);n=-c-v*a*beta**2;o=(a-2*v*c)*beta/2
        lam=(c+n)/2+(((c-n)/2)**2+o**2).sqrt()
        vals.append(max(-c.l,lam.h))
    return max(vals)


def check():
    import sympy as S
    from check_f8_combined_residual import clock_box
    b,z,W,N,U,k=S.symbols('b z W N U k',positive=True);v,a,s=S.symbols('v a s',real=True);c=3*v/(2*z)
    P=W+(1-v)*N;M=W-(1+v)*N
    q=c*(P*M-k*k*U*U)+a*(P*P-M*M)/4
    assert S.expand(q-(-c*k*k*U*U+c*W*W+(-c*(1-v*v)-v*a)*N*N+(a-2*v*c)*W*N))==0
    X,Y,Z=S.symbols('X Y Z',real=True);Qm=S.Matrix([[-c,0,0],[0,c,(a-2*v*c)/(2*S.sqrt(s))],[0,(a-2*v*c)/(2*S.sqrt(s)),-c-v*a/s]])
    D=S.diag(1,1,-1);assert S.simplify(Qm.subs(v,-v)+D*Qm*D)==S.zeros(3)
    # Characteristic polynomial of 2x2 normalized block.
    t=S.symbols('t');m=Qm[1:3,1:3];assert S.simplify((t*S.eye(2)-m).det()-((t-S.trace(m)/2)**2-((m[0,0]-m[1,1])/2)**2-m[0,1]**2))==0
    # Affine dependence on inverse normal coordinate is exact.
    x=S.symbols('x');m=Qm.subs(z,b/x);assert m.diff(x,2)==S.zeros(3)
    rows=[]
    for b0 in [Q(1),Q(3,4),Q(1,2),Q(1,4),Q(1,8),Q(1,12)]:
        # singleton b box, rate function derives physical coefficients itself
        box=((b0,b0),None,None,None);f,r=rate(box),rate(box,True);assert 0<f<Q(5,2) and 0<r<Q(5,2)
        rows.append([float(b0),float(f),float(r)])
    return dict(checks=16,rows=rows,scope='exact spectrum and rational endpoint upper bounds; norm rate, not energy rate')
if __name__=='__main__':print(json.dumps(check()))
