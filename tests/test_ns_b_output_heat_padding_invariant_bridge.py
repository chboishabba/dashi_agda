"""Same-source B output-heat normal form versus the obsolete fibre-mean covariance.

Original mathematical identity: parallelogram law, Leray/viscous Fourier
rate; existing DASHI theorem:
NSTriadKNFixedOutputPhysicalOutputRateNormalFormExact.agda.
Integration: NSTriadKNR650RateKernelCommutatorEndpointRound685Exact.agda.

No new original B regularity theorem or cutoff-uniform estimate is claimed.
"""
import sympy as s

def work(u,v):
    return s.simplify(2*s.re((s.conjugate(u).T*v)[0]))

def mass(p):
    return sum(x*x for x in p)

def split(p,q,nu=1):
    k=tuple(p[i]+q[i] for i in range(3))
    return (
        s.Rational(1,2)*nu*mass(k),
        s.Rational(1,2)*nu*sum((p[i]-q[i])**2 for i in range(3)),
        nu*(mass(p)+mass(q)))

def test_physical_shear_output_rate_and_centered_work():
    p=(1,0,0);q=(0,1,0)
    a=s.Matrix([-s.I/4,-s.I/4,s.Rational(1,4)])
    b=s.Matrix([-s.I/4,-s.I/4,-s.Rational(1,4)])
    M=a+b
    rates=[split(p,q),split(q,p)]
    assert all(common+centered==total for common,centered,total in rates)
    K=sum(total*work(M,x) for (_,_,total),x in zip(rates,(a,b)))
    common=rates[0][0]*work(M,M)
    centered=sum(center*work(M,x) for (_,center,_),x in zip(rates,(a,b)))
    assert (K,common,centered)==(2,1,1)

def test_zero_amplitude_high_rate_padding_changes_only_fibre_mean():
    p=(1,0,0);q=(0,1,0)
    a=s.Matrix([-s.I/4,-s.I/4,s.Rational(1,4)])
    b=s.Matrix([-s.I/4,-s.I/4,-s.Rational(1,4)])
    M=a+b
    values=[a,b]
    rates=[2,2]
    K=sum(r*work(M,v) for r,v in zip(rates,values))
    original_count_centering=2*(-K)+sum(rates)*work(M,M)
    assert original_count_centering==0
    for n in [16,32,64]:
        far=(n,0,0);other=(1-n,1,0)
        assert split(far,other)[2]==2*n*n-2*n+2
        extended_values=values+[s.zeros(3,1)]
        extended_rates=rates+[split(far,other)[2]]
        K_extended=sum(r*work(M,v) for r,v in zip(extended_rates,extended_values))
        common,centered,_=split(far,other)
        assert K_extended==K
        assert common==1
        assert work(M,extended_values[-1])==0
        new_mean_cov=len(extended_values)*(-K_extended)+sum(extended_rates)*work(M,M)
        assert new_mean_cov==split(far,other)[2]-2

def test_generic_signed_mixed_complex_cells_preserve_no_count_normal_form():
    p=(2,0,0);q=(0,3,4)
    a=s.Matrix([1+s.I,2-s.I,3])
    b=s.Matrix([s.I,1,2*s.I])
    z=s.zeros(3,1)
    vs=[a,b]
    pairs=[(p,q),(q,p)]
    def form(vs,pairs):
        M=sum(vs,s.zeros(3,1))
        rateWork=sum(split(p,q)[2]*work(M,v) for v,(p,q) in zip(vs,pairs))
        shared=split(p,q)[0]*work(M,M)
        diff=sum(split(p,q)[1]*work(M,v) for v,(p,q) in zip(vs,pairs))
        return rateWork,shared,diff
    out=form(vs,pairs)
    assert out[0]==out[1]+out[2]
    for n in [12,20,40]:
        # For fixed k=(2,3,4), append an arbitrary zero mixed cell.
        far=(n,0,0);other=(2-n,3,4)
        ext=form(vs+[z],pairs+[(far,other)])
        assert ext==out
