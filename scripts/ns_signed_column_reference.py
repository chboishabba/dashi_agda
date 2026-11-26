"""Signed Fourier-column bound, extending ns_polynomial_reference.
DASHI exact finite refinement of the existing polarized Leray estimate.
Periodic, mean-zero selected data only; not the universal R503/B4 theorem.
"""
from fractions import Fraction as Q
from itertools import product
from ns_polynomial_reference import (ZERO, add, scale, lam, dot, proj, check,
    norm, sqrt_bounds, polarized_growth, bernstein, residual, lin, eval_end,
    exp_upper, up, build, cos_mode, validate_polarized)


def port_bound(k,a,l):
    m=add(k,l)
    if not any(m):return Q(0)
    # Complex linear map P_m[(a.m) I+a m^T]P_l, divided by |m|.
    # Frobenius is an operator-norm upper bound; intersect with the
    # existing polarized bound |a|. All signs and phases are retained.
    ar,ai=a[:3],a[3:];x,y=dot(m,ar),dot(m,ai)
    sq=Q(0)
    for j in range(3):
        b=proj(l,tuple(int(i==j) for i in range(3))+(0,)*3)[:3]
        t=dot(m,b)
        w=proj(m,add(scale(x,b),scale(t,ar))+add(scale(y,b),scale(t,ai)))
        sq+=sum(z*z for z in w)
    return min(sqrt_bounds(sum(z*z for z in a))[1],sqrt_bounds(sq/Q(lam(m)))[1])


def column_growth(vertices,beta,max_radius=5):
    if beta<=0 or not vertices:raise ValueError('invalid column budget')
    V=max(norm(v) for v in vertices);base=polarized_growth(V,beta)
    R=V/beta
    # High modes are nonpositive by the previous global polarization
    # bound V|l|-beta|l|². Explicitly retain this infinite tail proof.
    if R<=1:return Q(0)
    if R>max_radius:return base
    radius=R.numerator//R.denominator;best=Q(0)
    for l in product(range(-radius,radius+1),repeat=3):
        l2=lam(l)
        if not l2 or l2>=R*R:continue
        if next(x for x in l if x)!=abs(next(x for x in l if x)):continue
        # Reality makes the opposite column identical. Convexity of the
        # sum of operator norms permits bounding on Bernstein vertices.
        # Min of two bounds need not be convex, so use the max vertex
        # bound separately for each port BEFORE summing.
        ks=set().union(*(v.keys() for v in vertices))
        bound=sum(max(port_bound(k,v.get(k,ZERO),l) for v in vertices) for k in ks)
        best=max(best,sqrt_bounds(l2)[1]*bound-beta*l2)
    return min(base,up(best))


def validate_column(path,initial,nu,budget=None,*,initial_tail=Q(0),max_radius=5):
    if type(nu) not in (Q,int) or nu<=0:raise ValueError('positive exact viscosity required')
    q=Q(nu,4) if budget is None else budget
    if type(q) not in (Q,int) or not 0<q<2*nu:raise ValueError('invalid strict budget')
    available=nu-Q(q,2);delta=min(Q(nu,8),Q(available,2));beta=available-delta
    if type(initial_tail) not in (Q,int) or not 0<=initial_tail<q:raise ValueError('invalid initial tail bound')
    check(initial);last=initial;error=Q(initial_tail);peak=error
    for dt,poly in path:
        if type(dt) not in (Q,int) or dt<=0 or not poly:raise ValueError('invalid interval')
        for v in poly:check(v)
        jump=norm(lin((1,last),(-1,poly[0])),True)
        growth=column_growth(bernstein(poly),beta,max_radius)
        rb=bernstein(residual(dt,poly,nu))
        c=dt*sum((norm(v,True) for v in rb),Q(0))/len(rb)
        error=up(exp_upper(dt*growth)*(error+jump+c))
        if error>=q:raise ValueError('strict error budget exceeded')
        peak=max(peak,error);last=eval_end(poly)
    return peak,up(norm(last,True)+error)


def run():
    from ns_polynomial_reference import fixture, bilinear
    import sympy as sp
    from itertools import product
    # Independent exact signed column reconstruction, projected inputs.
    cases=0
    k=(0,1,0);a=(Q(1),0,0,0,0,Q(1,2))
    for l in product(range(-1,2),repeat=3):
        if not any(l) or not any(m:=add(k,l)):continue
        b=proj(l,(1,2,3,-1,0,1));left=lin((1,bilinear({k:a},{l:b})),(1,bilinear({l:b},{k:a})))
        val=sum(x*x for x in left.get(m,ZERO));bound=port_bound(k,a,l)
        if val>bound**2*lam(m)*sum(x*x for x in b):raise AssertionError('signed column upper bound')
        cases+=1
    # Exact selected source fixture and its same physical polynomial path.
    u=fixture();path=build(u,2,Q(1,32),4)
    old=validate_polarized(path,u,Q(1));new=validate_column(path,u,Q(1))
    if not (new[0]<=old[0] and new[1]<=old[1] and new[1]<2):raise AssertionError('selected path comparison')
    print('port controls',cases,'legacy',tuple(map(float,old)),'column',tuple(map(float,new)),flush=True)
    # Rejection/fallback are explicit, never a truncation of positive columns.
    if column_growth([u],Q(1,100),max_radius=1)!=polarized_growth(norm(u),Q(1,100)):raise AssertionError('fallback')
    print('signed column refinement PASS',flush=True)

if __name__=='__main__':run()
