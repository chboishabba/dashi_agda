"""Coarse joint source-access inverse: passive two-mode port geometry.
Conditional finite reciprocal model, not an identified atmospheric mechanism.
"""
import sympy as S

def reverse_access(V,R,r,L,target,overhead=0):
    """Ideal reciprocal transformer between source and fixed load.
    x=n^2 L is reflected useful resistance. Series r is irreducible loss.
    """
    V,R,r,L,Y,C=map(S.Rational,(V,R,r,L,target,overhead))
    if min(R,L)<=0 or r<0 or min(Y,C)<0:raise ValueError('domain')
    A=R+r;W=Y+C
    if W==0:return dict(status='ZERO_TARGET',cap=V*V/(4*A))
    disc=V**4-4*W*A*V*V
    if disc<0 or V==0:return dict(status='EMPTY_ON_DOMAIN',cap=V*V/(4*A))
    xlo=(V*V-2*W*A-S.sqrt(disc))/(2*W)
    xhi=(V*V-2*W*A+S.sqrt(disc))/(2*W)
    assert S.simplify(xlo*xhi-A*A)==0
    return dict(status='CONDITIONAL_FIBRE',cap=V*V/(4*A),ratio_squared=(xlo/L,xhi/L))

def reciprocal_bridge(V,R,r,L,n):
    V,R,r,L,n=map(S.Rational,(V,R,r,L,n))
    assert min(R,L)>0 and r>=0 and n>=0
    i=V/(R+r+n*n*L);j=n*i
    natural=V*i;loss=(R+r)*i*i;out=L*j*j
    assert natural==loss+out
    return dict(source=natural,loss=loss,receiver=out)

def access_gap(V,R,r,L,n):
    V,R,r,L,n=map(S.Rational,(V,R,r,L,n))
    a=R+r;x=n*n*L
    w=reciprocal_bridge(V,R,r,L,n)
    gap=V*V*(a-x)**2/(4*a*(a+x)**2)
    assert V*V/(4*a)-w['receiver']==gap
    return gap

def joint_cycle(natural,driver,receiver,recovered,loss,aux,storage_delta,
                passive_upper,gain):
    """Disjoint external ports only: recovered is exported useful work,
    NOT internal modulation transfer. Inputs signed except declared costs.
    """
    N,D,Y,Z,L,C,U,P,g=map(S.Rational,(natural,driver,receiver,recovered,loss,aux,storage_delta,passive_upper,gain))
    assert min(Y,Z,L,C,P)>=0 and g>0
    residual=N+D-Y-Z-L-C-U
    net=Y+Z-D
    return dict(balance=residual,restored=U==0,net=net,margin=net-P-g,
                admitted_math=residual==0 and U==0 and net>=P+g,
                physical_admission=False)

def source_access_required(passive_upper,gain,loss,aux):
    P,g,L,C=map(S.Rational,(passive_upper,gain,loss,aux))
    assert min(P,L,C)>=0 and g>0
    return P+g+L+C

def run():
    # Fixed load: reciprocal access can improve mismatch, not matched cap.
    p=reciprocal_bridge(1,1,0,4,1)
    a=reciprocal_bridge(1,1,0,4,S.Rational(1,2))
    assert p['receiver']==S.Rational(4,25) and a['receiver']==S.Rational(1,4)
    assert access_gap(1,1,0,4,S.Rational(1,2))==0
    f=reverse_access(1,1,0,4,S.Rational(1,4))
    assert f['ratio_squared']==(S.Rational(1,4),)*2
    assert reverse_access(1,1,0,4,S.Rational(26,100))['status']=='EMPTY_ON_DOMAIN'
    # Same boundary, full restored balance, explicit costs.
    w=joint_cycle(S.Rational(1,2),0,S.Rational(1,4),0,S.Rational(1,4),0,0,S.Rational(4,25),S.Rational(1,100))
    assert w['admitted_math']
    w=joint_cycle(S.Rational(1,2),0,S.Rational(1,4),0,S.Rational(1,4),0,0,S.Rational(1,4),S.Rational(1,100))
    assert not w['admitted_math']
    assert source_access_required(S.Rational(1,4),S.Rational(1,100),S.Rational(1,4),0)==S.Rational(51,100)
    print('JOINT_ACCESS_PASS: fixed mismatch improvement, matched ceiling, inverse fibre, disjoint work')
if __name__=='__main__':run()
