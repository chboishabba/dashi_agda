"""Exact replenished reciprocal oscillator reference.
Reconstructed from documented M1 Hamiltonian, NOT original package replay.
Normalized linear fixed-coupling harmonic slice; no physical HF identification.
"""
import sympy as S

def harmonic(M,K,D,f,omega):
    M,K,D,f=map(S.Matrix,(M,K,D,f));w=S.sympify(omega)
    if w.is_positive is not True:raise ValueError('positive frequency')
    n=M.rows
    for A in (M,K,D):
        if A.shape!=(n,n) or A!=A.T or any(x.is_real is not True for x in A):
            raise ValueError('real symmetric matrices')
        if any(A[:j,:j].det().is_positive is not True for j in range(1,n+1)):
            raise ValueError('strictly positive reference metric')
    if f.shape!=(n,1):raise ValueError('force shape')
    Z=K-w*w*M+S.I*w*D
    q=Z.inv()*f;v=S.I*w*q
    work=S.simplify(S.re((v.H*f)[0])/2)
    heat=S.simplify((v.H*D*v)[0]/2)
    assert S.simplify(work-heat)==0
    # All q,v repeat after 2pi/w. Strict damping and positive K imply
    # asymptotic stability by the autonomous energy/LaSalle argument.
    return dict(displacement=q,velocity=v,source_power=work,dissipation=heat,
                periodic=True,physical_admission=False)

def chain(k1,k2,loss,load,source,driver=0,w=1):
    k1,k2,load,w=map(S.sympify,(k1,k2,load,w))
    if any(x.is_nonnegative is not True for x in (k1,k2,load)):raise ValueError('passive coefficients')
    M=S.eye(3)
    b=S.Matrix([1,-1,0]);c=S.Matrix([0,1,-1])
    K=S.eye(3)+k1*b*b.T+k2*c*c.T
    D=S.diag(*loss);D[0,0]+=load
    f=S.Matrix([driver,0,source]);r=harmonic(M,K,D,f,w);v=r['velocity']
    y=S.simplify(load*S.conjugate(v[0])*v[0]/2)
    N=S.simplify(S.re(S.conjugate(v[2])*source)/2)
    C=S.simplify(S.re(S.conjugate(v[0])*driver)/2)
    L=S.simplify(sum(loss[i]*S.conjugate(v[i])*v[i]/2 for i in range(3)))
    assert S.simplify(N+C-y-L)==0
    return dict(r,receiver=y,natural=N,controller=C,loss=L,net=S.simplify(y-C))

def source_cap(force,damping):
    f,d=map(S.sympify,(force,damping))
    if d.is_positive is not True:raise ValueError('positive damping')
    return S.simplify(f*S.conjugate(f)/(8*d))

def reverse_residual(force,damping,target,loss=0):
    f,d,y,l=map(S.sympify,(force,damping,target,loss))
    assert d.is_positive and y.is_nonnegative and l.is_nonnegative
    cap=source_cap(f,d);head=S.simplify(cap-y-l)
    return dict(cap=cap,headroom=head,empty=head.is_negative is True,
                velocity_center=f/(2*d),radius_squared=S.simplify(2*head/d))

def run():
    loss=[S.Integer(1)]*3
    a=chain(1,1,loss,1,1);b=chain(1,0,loss,1,1)
    assert b['receiver']==0 and a['receiver']>0
    assert a['net']<=source_cap(1,1)==S.Rational(1,8)
    off=chain(1,1,loss,1,0,1)
    assert off['net']<=0
    r=reverse_residual(1,1,S.Rational(1,4));assert r['empty']
    assert reverse_residual(1,1,S.Rational(1,8))['radius_squared']==0
    print('REPLENISHED_HARMONIC_PASS', 'receiver',a['receiver'],'natural',a['natural'],'loss',a['loss'],'cap',source_cap(1,1))
if __name__=='__main__':run()
