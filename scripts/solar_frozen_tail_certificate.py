"""Exact finite rational source-off stage map and reachable-tail certificate.

The actual stage order is consumed from the original cone scheduler receipt.
No dense global midpoint substitution. Restrict to constant generator and
zero force with no material event. This does not certify a changing tail.
"""
import sympy as S

def rational(x):
    return S.Rational(float(x)) if isinstance(x,float) else S.Rational(x)

def tail_stage_matrix(H,dt,receipt):
    H=S.Matrix([[rational(v) for v in row] for row in H])
    h=rational(dt); d=H.rows
    if d!=H.cols or h<=0: raise ValueError('invalid frozen tail generator')
    T=S.eye(d); accounted=S.zeros(d)
    for item in receipt['events']:
        if item.get('source_roots') or item.get('work_J')!=0.:
            raise ValueError('tail receipt contains forcing')
        ix=item['coordinates']; a=H.extract(ix,ix)
        if item['face_id'] is not None:
            if len(ix)!=2: raise ValueError('invalid indexed face')
            a[0,0]=a[1,1]=0
        if not (-(a+a.T)).is_positive_semidefinite:
            raise ValueError('nonpassive frozen stage')
        for j,i in enumerate(ix):
            for k,l in enumerate(ix):
                if item['face_id'] is None or j!=k:
                    if accounted[i,l]!=0: raise ValueError('overlapping nonzero generator entry')
                    accounted[i,l]=a[j,k]
        I=S.eye(len(ix)); C=(I-h*a/2).inv()*(I+h*a/2)
        rows=C*T[ix,:]
        for j,i in enumerate(ix): T[i,:]=rows[j,:]
    if accounted!=H: raise ValueError('generator not covered by scheduler receipt')
    return T

def reachable_tail_certificate(T,x,max_power=8,max_dyadic=24):
    """Exact contraction on the orbit span, not all coordinate directions.

    For basis K of span{x,Tx,...}, TK=KC. G=K^T K. A rational rho2<1
    with rho2 G-(C^m)^T G C^m PSD proves geometric decay every m steps.
    If no certificate is found, do not infer instability.
    """
    T=S.Matrix(T); x=S.Matrix(x); d=T.rows
    if T.cols!=d or x.shape!=(d,1) or not all(v.is_Rational for v in list(T)+list(x)):
        raise ValueError('exact rational frozen chart required')
    if not (S.eye(d)-T.T*T).is_positive_semidefinite:
        raise ValueError('noncontractive frozen step')
    if x==S.zeros(d,1):
        return dict(status='ZERO_STATE',reachable_rank=0,block_steps=1,rho_squared='0',field_return_proved=True)
    columns=[]; y=x
    while len(columns)<d:
        K=S.Matrix.hstack(*(columns+[y]))
        if K.rank()!=len(columns)+1: break
        columns.append(y); y=T*y
    K=S.Matrix.hstack(*columns);G=K.T*K; C=G.inv()*K.T*T*K
    if T*K!=K*C: raise ArithmeticError('reachable span not invariant')
    # A preserved left component is an exact obstruction to zero return.
    for v in (T.T-S.eye(d)).nullspace():
        if (v.T*x)[0]!=0:
            return dict(status='NONZERO_CONSERVED_COMPONENT',reachable_rank=K.cols,
                        invariant_value=str((v.T*x)[0]),field_return_proved=False,
                        exact_zero_return_obstructed=True)
    for m in range(1,max_power+1):
        B=(C**m).T*G*C**m
        if not (G-B).is_positive_definite: continue
        for j in range(1,max_dyadic+1):
            rho2=1-S.Rational(1,2**j)
            if (rho2*G-B).is_positive_semidefinite:
                return dict(status='EXACT_REACHABLE_CONTRACTION',reachable_rank=K.cols,
                    block_steps=m,rho_squared=str(rho2),field_return_proved=True,
                    scope='constant rational zero-force stage map; no material events')
    return dict(status='NO_CONTRACTION_CERTIFICATE',reachable_rank=K.cols,
                field_return_proved=False,exact_zero_return_obstructed=False)
