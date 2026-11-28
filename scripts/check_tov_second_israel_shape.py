"""Original TOV two-face second shape jets and necessary Israel correction.
The background two analytic continuations are compared at the displaced wall;
this is a source/junction compatibility obstruction, not a full solution.
"""
import sympy as s

def main():
    r, l, e, phi, psi=s.symbols('r l eps phi psi',real=True)
    M=l*(2+l)/15
    f=1-l*(2+l)*(r*r/3-r**4/5)
    F=1-2*M/r
    P=(2+l)*(s.Rational(1,3)-r*r/5)/2-(1-r*r)**2/2
    ni=r*l*P/f
    no=M/(r*r*F)
    # Jointly matched background data through first radial normal derivative.
    assert all(s.cancel((z).subs(r,1))==0 for z in (f-F,s.diff(f-F,r),ni-no,s.diff(ni-no,r)))
    # Factor the first unmatched radial jets (density gradient is nonzero).
    d2f=s.factor(s.diff(f-F,r,2).subs(r,1))
    d2nu=s.factor(s.diff(ni-no,r,2).subs(r,1))
    assert d2f!=0 and d2nu!=0
    R=1+e*phi+e*e*psi/2
    # Mixed K eigenvalues K^theta_theta=sqrt(f)/r, K^tau_tau=sqrt(f)*nu.
    Kthi=s.sqrt(f)/r; Ktho=s.sqrt(F)/r
    Kti=s.sqrt(f)*ni; Kto=s.sqrt(F)*no
    for z in (Kthi-Ktho,Kti-Kto):
        # The common moving-surface first jet vanishes; second jet remains.
        assert s.simplify(z.subs(r,1))==0
        assert s.simplify(s.diff(z,r).subs(r,1))==0
        shape=s.simplify(s.diff(z,r,2).subs(r,1))
        assert shape!=0
        raw=s.diff(z.subs(r,R),e,2).subs(e,0)
        assert s.simplify(raw-phi*phi*shape)==0
    Kth_jump=s.simplify(s.diff(Kthi-Ktho,r,2).subs(r,1))
    Kt_jump=s.simplify(s.diff(Kti-Kto,r,2).subs(r,1))
    # For arbitrary first-order perturbations, J2 demands second-order
    # *dynamical* extrinsic corrections cancel these shape coefficients.
    delta2th,delta2t=s.symbols('delta2th delta2t')
    assert s.simplify((delta2th+phi*phi*Kth_jump).subs(delta2th,-phi*phi*Kth_jump))==0
    assert s.simplify((delta2t+phi*phi*Kt_jump).subs(delta2t,-phi*phi*Kt_jump))==0
    print('PASS background matching to first jet, nonzero second shape jets',flush=True)
    print('f_second_jump:',d2f,'nu_second_jump:',d2nu,flush=True)
    print('Ktheta_second_jump:',s.factor(Kth_jump),'Ktau_second_jump:',s.factor(Kt_jump),flush=True)
    print('OPEN dynamical second metric/normal jets, common induced metric and GHY corner terms',flush=True)

if __name__=='__main__':main()
