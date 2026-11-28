"""Exact multiport source-access ceiling and signed inverse residual.
Finite real source coordinates, SPD dissipation metric; no measured admission.
"""
import sympy as S

def zero(x):return all(S.simplify(v)==0 for v in x)

def metric(R):
    R=S.Matrix(R)
    if R.rows!=R.cols or R!=R.T or any(v.is_real is not True for v in R):raise ValueError('real symmetric metric')
    if any(R[:k,:k].det().is_positive is not True for k in range(1,R.rows+1)):raise ValueError('SPD required')
    return R

def source_geometry(R,v,K):
    """K spans reachable current subspace. Exact signed complement.
    The optimum is an outer bound unless a reciprocal termination realizes it.
    """
    R=metric(R);v,K=map(S.Matrix,(v,K))
    if v.shape!=(R.rows,1) or K.rows!=R.rows or K.rank()!=K.cols:raise ValueError('chart')
    full=R.inv()*v/2
    if K.cols:
        q=(K.T*R*K).inv()*K.T*v/2;i=K*q
    else:i=S.zeros(R.rows,1)
    residual=full-i
    cap=S.simplify((i.T*R*i)[0]);all_cap=S.simplify((full.T*R*full)[0])
    assert zero(K.T*R*residual)
    assert S.simplify(all_cap-cap-(residual.T*R*residual)[0])==0
    return dict(current=i,full_current=full,residual=residual,cap=cap,full_cap=all_cap,
                residual_work=all_cap-cap,physical_admission=False)

def reverse_gain(R,v,K,baseline,gain,cost):
    a=source_geometry(R,v,K);b,g,c=map(S.Rational,(baseline,gain,cost))
    if min(b,c)<0 or g<=0:raise ValueError('work domain')
    target=b+g+c;return dict(a,target=target,margin=a['cap']-target,
        status='EMPTY_ON_CURRENT_SUBSPACE' if a['cap']<target else 'CONDITIONAL_FIBRE')

def termination(R,v,K):
    """Construct a rank-one PSD reciprocal load achieving accessible cap.
    K is assumed to be implementable by an ideal reciprocal coordinate map.
    """
    R=metric(R);v,K=map(S.Matrix,(v,K));a=source_geometry(R,v,K)
    if a['cap']==0:return dict(a,load=None)
    G=K.T*R*K;e=K.T*v;q=G.inv()*e/2
    z=G*q;L=z*z.T/(q.T*z)[0]
    assert zero((G+L)*q-e)
    assert S.simplify((q.T*L*q)[0]-a['cap'])==0
    return dict(a,load=L,coordinate_current=q)

def run():
    R=S.Matrix([[2,1],[1,2]]);v=S.Matrix([1,2]);K=S.Matrix([1,0])
    a=termination(R,v,K);b=termination(R,v,S.eye(2))
    assert a['cap']==S.Rational(1,8) and b['cap']==S.Rational(1,2)
    assert a['residual_work']==S.Rational(3,8)
    assert reverse_gain(R,v,K,S.Rational(1,8),S.Rational(1,100),0)['status']=='EMPTY_ON_CURRENT_SUBSPACE'
    assert reverse_gain(R,v,S.eye(2),S.Rational(1,8),S.Rational(1,100),0)['status']=='CONDITIONAL_FIBRE'
    assert reverse_gain(R,v,S.eye(2),S.Rational(1,2),S.Rational(1,100),0)['status']=='EMPTY_ON_CURRENT_SUBSPACE'
    # Signed orientation, not magnitude: opposite source direction changes access.
    assert source_geometry(S.eye(2),S.Matrix([1,-1]),S.Matrix([1,1]))['cap']==0
    assert source_geometry(S.eye(2),S.Matrix([1,-1]),S.Matrix([1,-1]))['cap']==S.Rational(1,2)
    print('MULTIPORT_ACCESS_PASS: exact projection gap, reciprocal PSD load, signed orientation, matched comparator')
if __name__=='__main__':run()
