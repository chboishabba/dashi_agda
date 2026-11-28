"""Exact modular observability of the original zero-exchange right-limit split.
Full rank modulo a good prime proves rational full rank, hence strict block
contraction on the occupied coordinates. Deficient modular rank proves no
obstruction. This is the finite split map, not continuum Maxwell stability.
"""
from fractions import Fraction as F
import numpy as np
from solar_matrix_storage import block


def q(x):return F(float(x))


def mod(x,p):
    if x.denominator%p==0:raise ZeroDivisionError('bad reduction prime')
    return (x.numerator%p)*pow(x.denominator,-1,p)%p


def reference_observability(H,dt,receipt,occupied,field_size,prime=65521):
    """Consume original stage receipts; verify decoupling, support and passivity.
    The quantitative margin is factored to avoid huge rational denominators.
    """
    from sympy import isprime
    if not isprime(prime) or prime>2**23:raise ValueError('small prime required for safe int64 products')
    d=H.shape[0];n=int(field_size);h=q(dt);occ=np.asarray(occupied,bool)
    if H.shape!=(d,d) or not 0<n<=d or occ.shape!=(d,) or not occ[:n].all() or h<=0 or n*prime**2>=2**63:
        raise ValueError('invalid right-limit chart')
    T=np.eye(n,dtype=np.int64); seen=set();local=set();damped=[];losses=[];den=[];current_margin=[]
    # Exact operator support coverage including all dormant stage coordinates.
    required={(int(i),int(j)) for i,j in zip(*H.nonzero())};remote_seen=False
    for event in receipt['events']:
        if event.get('source_roots') or event.get('work_J')!=0.:raise ValueError('forced tail receipt')
        ix=np.array(event['coordinates'],int);B=block(H,ix);remote=event['face_id'] is not None
        if len(set(ix))!=len(ix) or np.any(ix<0) or np.any(ix>=d):raise ValueError('invalid stage coordinates')
        if remote:
            remote_seen=True
            if len(ix)!=2:raise ValueError('remote stage must have two coordinates')
            B=B.copy();np.fill_diagonal(B,0)
        else:
            if remote_seen:raise ValueError('local losses must precede remote stages')
            if local.intersection(ix):raise ValueError('overlapping local coordinates')
            local.update(ix)
        for j,k in zip(*B.nonzero()):
            pair=(int(ix[j]),int(ix[k]))
            if pair in seen:raise ValueError('duplicated nonzero entry')
            seen.add(pair)
        if np.all(ix<n):
            if remote:
                if B[0,1]!=-B[1,0]:raise ValueError('nonreciprocal field stage')
                a=h*q(B[0,1])/2;v=(1-a*a)/(1+a*a);w=2*a/(1+a*a)
                den.extend([v.denominator,w.denominator]);u=mod(v,prime);r=mod(w,prime)
                i,j=ix;x,y=T[i].copy(),T[j].copy();T[i]=(u*x+r*y)%prime;T[j]=(-r*x+u*y)%prime
            else:
                if len(ix)!=1 or B[0,0]>0:raise ValueError('field local scalar loss required')
                i=int(ix[0]);a=h*q(B[0,0])/2;v=(1+a)/(1-a)
                if B[0,0]<0:
                    damped.append(i);losses.append(1-v*v)
                den.append(v.denominator);T[i]=mod(v,prime)*T[i]%prime
        elif remote:
            if np.any(B):raise ValueError('right-limit remote material exchange nonzero')
        else:
            if np.any(ix<n):raise ValueError('mixed local field/current coordinates')
            active=occ[ix]
            if np.any(B[~active,:]) or np.any(B[:,~active]):raise ValueError('inactive slot not invariant')
            if np.any(active):
                C=B[np.ix_(active,active)];off=C.copy();np.fill_diagonal(off,0)
                if np.any(np.diag(C)>=0) or not np.array_equal(off,-off.T):raise ValueError('active current block lacks strict diagonal damping')
                nu=min(-q(v) for v in np.diag(C));norm=sum((abs(q(v)) for v in C.ravel()),F(0))
                current_margin.append(2*h*nu/(1+h*norm/2)**2)
    if seen!=required or local!=set(range(d)):raise ValueError('incomplete reference stage coverage')
    basis={};selected=[];rows=np.eye(n,dtype=np.int64)[damped];steps=0
    for k in range(n):
        steps=k+1
        for i,row in zip(damped,rows):
            v=row.copy()
            for j,b in sorted(basis.items()):v=(v-v[j]*b)%prime
            nz=np.flatnonzero(v)
            if len(nz):
                j=int(nz[0]);basis[j]=v*pow(int(v[j]),-1,prime)%prime;selected.append((k,i))
        if len(basis)==n:break
        rows=(rows@T)%prime
    full=len(basis)==n
    # Q=product of all stage denominators; T entries have denominator dividing Q.
    # |det O|>=Q^(-sum selected k), row norms <=1. Thus sigma_min(O)^2
    # >= Q^(-2 sum k)/n^(n-1). Store Q by its conservative power-of-two bound.
    # Energy drop over m steps >= min(losses)*||O x||^2.
    exp2=sum(v.bit_length() for v in den)*2*sum(k for k,i in selected)
    exp2+=(n-1)*n.bit_length()
    margin_loss=min(losses,default=F(0))
    # For full occupied contraction, also bound the decoupled current block.
    if current_margin:margin_loss=min(margin_loss,min(current_margin))
    return dict(status='EXACT_FULL_OBSERVABILITY' if full else 'MODULAR_RANK_INCOMPLETE',prime=prime,
        field_size=n,occupied_size=int(occ.sum()),rank=len(basis),block_steps=steps,
        selected_observations=[list(v) for v in selected],damped_field_coordinates=damped,
        strict_occupied_block_contraction=full,qualitative_changing_tail_decay_conditional=full,
        energy_drop_lower_factor=str(margin_loss) if full else None,
        energy_drop_lower_power_of_two=exp2 if full else None,
        # ||T^m||<=1 - factor*2^(-exp2-1); quantitative bound very conservative.
        reference_norm_margin_power_of_two=exp2+1 if full else None,
        physical_admission=False,continuum_admission=False)
