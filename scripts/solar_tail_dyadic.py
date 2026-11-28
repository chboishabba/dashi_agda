"""Certified dyadic block powers on the same rational right-limit field map.
No spectral radius estimate, float eigenvalues, or physical admission.
"""
from fractions import Fraction as F
from math import isqrt
import numpy as np
from solar_matrix_storage import block
from solar_tail_observability import reference_observability


def ceil_div(a,b):return -(-a//b)


def sqrt_ceil(x):
    y=isqrt(x);return y+(y*y<x)


def dyadic_field_map(H,dt,receipt,occupied,field_size,bits=192,field_diagonal=None):
    """Exact rational stage actions rounded on a common fixed dyadic grid.
    Each rounding has Frobenius error <= nrows*n/scale (conservative).
    Every exact stage is nonexpansive, so these residuals telescope additively.
    """
    if bits<32 or bits>4096:raise ValueError('invalid dyadic precision')
    obs=reference_observability(H,dt,receipt,occupied,field_size)
    n=field_size;h=F(float(dt));scale=1<<bits;T=np.eye(n,dtype=object)*scale;err=0
    current_margin=F(1)
    if field_diagonal is not None:
        field_diagonal=list(map(F,field_diagonal))
        if len(field_diagonal)!=n or any(v>0 for v in field_diagonal):raise ValueError('invalid exact field diagonal')
    for e in receipt['events']:
        ix=np.array(e['coordinates'],int); B=block(H,ix)
        if np.any(ix>=n):
            if e['face_id'] is None and np.any(np.asarray(occupied)[ix]):
                C=B[np.ix_(np.asarray(occupied)[ix],np.asarray(occupied)[ix])]
                nu=min(-F(float(v)) for v in np.diag(C));norm=sum((abs(F(float(v))) for v in C.ravel()),F(0))
                current_margin=min(current_margin,2*h*nu/(1+h*norm/2)**2)
            continue
        a=h*(field_diagonal[int(ix[0])] if field_diagonal is not None and e['face_id'] is None else F(float(B[0,0] if e['face_id'] is None else B[0,1])))/2
        if e['face_id'] is None:
            v=(1+a)/(1-a);i=int(ix[0]);T[i]=T[i]*v.numerator//v.denominator;err+=n
        else:
            if not a:continue
            p,q=a.numerator,a.denominator;den=q*q+p*p;u=q*q-p*p;v=2*p*q
            i,j=ix;x,y=T[i].copy(),T[j].copy();T[i]=(u*x+v*y)//den;T[j]=(-v*x+u*y)//den;err+=2*n
    return T,err,scale,current_margin,obs


def dyadic_block_certificate(H,dt,receipt,occupied,field_size,bits=192,max_power=96):
    """Return exact norm upper on T^(2^k), or explicit inconclusive result.
    Square the integer approximation; add exact operator-norm error radius.
    Gram row sums bound the squared norm; the current margin is independent.
    """
    if not 0<=max_power<=256:raise ValueError('invalid power cap')
    A,e,Q,cm,obs=dyadic_field_map(H,dt,receipt,occupied,field_size,bits)
    n=field_size;history=[];best=None
    for k in range(max_power+1):
        G=A.T@A;g=max(sum(abs(v) for v in row) for row in G)
        bound=F(sqrt_ceil(int(g))+e,Q)
        m=1<<k; cb=1/(1+m*cm/2)
        rho=max(bound,cb) if obs['occupied_size']>n else bound
        if k%8==0 or rho<1 or k==max_power:
            history.append(dict(power=k,steps=m,field_norm_upper=float(bound),occupied_norm_upper=float(rho),rounding_radius=float(F(e,Q))))
        if rho<1:
            best=dict(power=k,block_steps=m,rho_upper_exact=str(rho),margin_exact=str(1-rho),
                      step_error_threshold_exact=str((1-rho)/m));break
        if k<max_power:
            A=(A@A)//Q
            e=2*e+ceil_div(e*e,Q)+n
    return dict(status='EXACT_DYADIC_BLOCK' if best else 'NO_DYADIC_MARGIN_WITHIN_CAP',bits=bits,
                certificate=best,history=history,modular_rank=obs['rank'],physical_admission=False)


def congruence_margin(A,e,Q,k,current_margin,bits):
    """Find a rational positive-definiteness witness; floating search only.
    Cholesky and triangular inverse propose a preconditioner. Acceptance uses
    only integer congruence and strict row diagonal dominance.
    """
    import mpmath as mp
    n=len(A);G=A.T@A;I=np.eye(n,dtype=object)
    with mp.workprec(2*bits+64):
        def propose(j):
            # Norm upper 1-2^-j for the exact block, including rounding radius.
            target=Q-(Q>>j)-e
            if target<=0:return None
            D=target*target*I-G
            try:L=mp.cholesky(mp.matrix(D.tolist()))
            except ValueError:return None
            return D,L
        lo=0;hi=bits-1
        if propose(hi) is None:return None
        while hi-lo>1:
            j=(lo+hi)//2
            if propose(j) is None:lo=j
            else:hi=j
        D,L=propose(hi)
        # Solve L B=I by forward substitution, then dyadically quantize.
        B=mp.matrix(n)
        for j in range(n):
            for i in range(j,n):
                B[i,j]=((1 if i==j else 0)-sum(L[i,t]*B[t,j] for t in range(j,i)))/L[i,i]
        factor=mp.mpf(2)**(2*bits)
        Z=np.array([[int(mp.nint(B[i,j]*factor)) for j in range(n)] for i in range(n)],dtype=object)
    C=Z@D@Z.T
    slack=min(int(C[i,i])-sum(abs(int(C[i,j])) for j in range(n) if i!=j) for i in range(n))
    if slack<=0:return None
    m=1<<k;rho=max(1-F(1,1<<hi),1/(1+m*current_margin/2))
    return dict(power=k,block_steps=m,rho_upper_exact=str(rho),margin_exact=str(1-rho),
        step_error_threshold_exact=str((1-rho)/m),gram_margin_bits=hi,
        positive_congruence_slack_bits=slack.bit_length(),rounding_radius_exact=str(F(e,Q)))


def preconditioned_block_certificate(H,dt,receipt,occupied,field_size,bits=256,powers=(32,48,64,80,96),field_diagonal=None,uniform_current_margin=None):
    """Search exact certified margins; no guarantee of a practical horizon."""
    if not powers or any(int(k)!=k or not 0<=k<=256 for k in powers):raise ValueError('invalid power list')
    A,e,Q,cm,obs=dyadic_field_map(H,dt,receipt,occupied,field_size,bits,field_diagonal)
    if uniform_current_margin is not None:
        cm=min(cm,F(uniform_current_margin))
        if cm<=0:raise ValueError('positive uniform current margin required')
    n=field_size;found=[]
    for k in range(max(powers)+1):
        if k in powers:
            candidate=congruence_margin(A,e,Q,k,cm,bits)
            if candidate is not None:found.append(candidate)
        if k<max(powers):A=(A@A)//Q;e=2*e+ceil_div(e*e,Q)+n
    best=max(found,key=lambda c:F(c['step_error_threshold_exact']),default=None)
    return dict(status='EXACT_PRECONDITIONED_BLOCK' if best else 'NO_CERTIFIED_MARGIN',bits=bits,
        certificate=best,candidates=found,modular_rank=obs['rank'],
        exact_field_diagonal_override=field_diagonal is not None,uniform_current_margin_exact=str(cm),physical_admission=False)
