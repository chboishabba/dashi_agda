"""AY: exact fixed-wall initial Einstein acceleration compatibility algebra."""
import sympy as s

def audit():
    a,b,c,d,e,f,j,l,N=s.symbols('a b c d e f j l N',real=True)
    M=s.Matrix([[a,b,c],[b,d,e],[c,e,f]]); I=s.eye(3)
    kp,km=M+j*I/2,M-j*I/2
    J2=s.Matrix([[s.Symbol('J'+str(min(i,k))+str(max(i,k))) for k in range(3)] for i in range(3)])
    expand=lambda X:X.applyfunc(s.expand)
    # In common orthonormal spatial wall frame, J2=[partial_n k_ab]
    # with k_ab=1/2 partial_n H_ab (covariant components).
    Ricjump=-J2-s.trace(kp)*kp+s.trace(km)*km+2*(kp*kp-km*km)
    assert expand(Ricjump-(-J2+j*M-j*s.trace(M)*I))==s.zeros(3)
    Hessjump=N*((l+j/2)*kp-(l-j/2)*km)
    assert expand(Hessjump-N*j*(M+l*I))==s.zeros(3)
    acc=2*N*(Hessjump-N*Ricjump)
    assert expand(acc-2*N**2*(J2+j*(s.trace(M)+l)*I))==s.zeros(3)
    scalarjump=-2*s.trace(J2)+3*s.trace(kp*kp-km*km)-(s.trace(kp)**2-s.trace(km)**2)
    assert s.expand(scalarjump+2*s.trace(J2))==0
    assert expand(acc.subs(l,-s.trace(M))-2*N**2*J2)==s.zeros(3)
    # Trace-free tensor perturbation is invisible to scalar constraint.
    test=s.diag(1,-1,0)
    assert s.trace(test)==0 and test!=s.zeros(3)
    # Given arbitrary current jets with scalar residuals Rp-2Lambda,
    # Rm-2Lambda and difference -2 tr J2, adjust both covariant jets.
    rp=s.Symbol('rp'); rm=rp+2*s.trace(J2)
    TF=J2-s.trace(J2)*I/3
    Dp=-TF/2+rp*I/6; Dm=TF/2+rm*I/6
    assert expand(J2+Dp-Dm)==s.zeros(3)
    assert s.expand(rp-2*s.trace(Dp))==0 and s.expand(rm-2*s.trace(Dm))==0
    print('PASS two-sided collar correction pays both scalar seam values and full second jet')
    print('PASS generic spatial Ricci/Hessian jump, acceleration BIDI, scalar trace and trace-free negative control')

if __name__=='__main__':audit()
