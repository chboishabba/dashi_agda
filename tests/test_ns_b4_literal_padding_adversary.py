"""Regression for the literal noncore/core B4 cutoff-padding no-go.

Two active ordered physical cells remain unchanged at every N, while
zero-amplitude high-high physical incidences alter centering moments.
Failure is *not* automatically a counterexample to a payment with an
unconstrained N-dependent localED input.
"""
import importlib.util
from pathlib import Path
from fractions import Fraction

P=Path(__file__).resolve().parents[1]/"scripts/ns_b4_literal_padding_adversary.py"
spec=importlib.util.spec_from_file_location("ns_b4_padding",P)
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

def test_authoritative_output_and_exact_two_core_cells():
    assert module.K==(1,1,0)
    assert module.region(module.P,module.Q)=="core"
    assert module.region(module.Q,module.P)=="core"
    assert module.region((10,0,0),(-9,1,0))=="noncore"

def test_literal_b4_padding_exact_certificates():
    results={n:module.certificate(n) for n in (4,8,9,16,24,36,40)}
    assert results[4]["signed_defect"]=="0"
    assert results[8]["signed_defect"]=="0"
    for n in (9,16,24,36,40):
        assert results[n]["core_rows"]==5474
        assert results[n]["literal_core_companion"]=="1345859672"
    assert results[9]["signed_defect"]=="185520"
    assert results[16]["signed_defect"]=="16776416"
    assert results[24]["signed_defect"]=="130871520"
    assert results[36]["signed_defect"]=="988633056"
    assert results[40]["signed_defect"]=="1671172320"
    assert results[36]["defect_exceeds_half_companion"]
    assert results[40]["defect_exceeds_half_companion"]

def test_no_renormalization_by_ignoring_zero_cells():
    n8=module.certificate(16)
    n16=module.certificate(40)
    assert n8["noncore_zero_amplitude_rows"]==28318
    assert n16["noncore_zero_amplitude_rows"]==512926
    assert Fraction(n16["signed_defect"])>Fraction(n8["signed_defect"])
    assert n16["literal_core_companion"]==n8["literal_core_companion"]

def test_unbounded_positive_subfamily_of_zero_amplitude_rows():
    # For each integer m>=10, p=(m,0,0), q=(1-m,1,0) is a noncore
    # row when cutoff N>=m. Its rate excess is exactly 2*m*(m-1).
    for m in (10,11,20,30,50):
        p=(m,0,0)
        q=(1-m,1,0)
        assert module.region(p,q)=="noncore"
        assert sum(x*x for x in p+q)-2==2*m*(m-1)
    assert sum(2*m*(m-1) for m in range(10,41)) <= int(
        module.certificate(40)["signed_defect"])


def test_selected_shear_is_genuine_unforced_solution_and_modal_R440_is_invariant():
    # u(t)=2*exp(-t)*(cos(x)+cos(y))*e_z is divergence-free.
    # u·grad u = u_z ∂_z u = 0; -Delta u0 = u0.
    # The two active H+ x H- cells have A,B as below;
    # this is exact Gaussian-rational arithmetic with denominator 4.
    from fractions import Fraction as F
    # Complex stored as pairs (real,imag), all components exact.
    A=((F(0),F(-1,4)),(F(0),F(-1,4)),(F(1,4),F(0)))
    B=((F(0),F(-1,4)),(F(0),F(-1,4)),(F(-1,4),F(0)))
    M=tuple((a[0]+b[0],a[1]+b[1]) for a,b in zip(A,B))
    assert M==((F(0),F(-1,2)),(F(0),F(-1,2)),(F(0),F(0)))
    normM=sum(z[0]**2+z[1]**2 for z in M)
    assert normM==F(1,2)
    rweighted=tuple((2*z[0],2*z[1]) for z in M)
    # Unlike full-fibre covariance, modal R440 weighted amplitude stays 2*M.
    assert all(rweighted[j]==(2*M[j][0],2*M[j][1]) for j in range(3))
    # W(M,2M)=2*Re(conj(M)·(2M))=2.
    assert 2 * 2 * normM == 2
    # Output k=(1,1,0) has |k|²=2, so the true centered modal rate is ZERO.
    assert all(rweighted[j]==(sum(x*x for x in module.K)*M[j][0],
                             sum(x*x for x in module.K)*M[j][1])
               for j in range(3))


def test_physical_local_ED_source_cannot_absorb_padding():
    # Exactly R219 physicalModalED + R109 pairKernel + R469 selectedTriadValue.
    # E(±e_x)=E(±e_y)=1, D=squared_frequency*E=1.
    modes={module.P, module.Q, tuple(-v for v in module.P),
           tuple(-v for v in module.Q)}
    energy={p:Fraction(1) for p in modes}
    dissipation={p:Fraction(sum(c*c for c in p))*energy[p] for p in modes}
    assert sum(energy.values())==4
    assert sum(dissipation.values())==4

    def pair_ed(p,q):
        return dissipation[p]*energy[q]+energy[p]*dissipation[q]

    fixed_output_pairs={(p,q) for p in modes for q in modes
                        if tuple(p[j]+q[j] for j in range(3))==module.K}
    assert fixed_output_pairs=={(module.P,module.Q),
                                (module.Q,module.P)}
    selected_output_ED=sum(pair_ed(p,q) for p,q in fixed_output_pairs)
    assert selected_output_ED==4
    assert sum(pair_ed(p,q) for p in modes for q in modes)==32

    for n in (9,16,24,36,40):
        r=module.certificate(n)
        assert r["physical_modal_energy"]=="4"
        assert r["physical_modal_dissipation"]=="4"
        assert r["literal_R109_global_selected_ED_bound"]=="32"
        assert r["literal_R219_R469_output_localED_bound"]=="4"
    assert Fraction(module.certificate(40)
                    ["necessary_cD_lower_bound_at_theta_half"])>0

def test_any_fixed_uniform_payment_coefficient_eventually_fails():
    # Strict half-margin thetaD<1/2; output local ED<=4. For arbitrary
    # fixed cD (even extremely large), the explicit noncore positive
    # subfamily has cubic growth and core mass stabilizes.
    Mcore=Fraction(module.certificate(9)["literal_core_companion"])
    def lower_subfamily(N):
        # 2*sum_(m=10)^N m(m-1) = (2/3)*(N^3-N-720).
        # Closed form prevents O(N) execution for huge adversarial cD.
        return 0 if N < 10 else 2*(N*(N*N-1)-720)//3
    assert lower_subfamily(40)==42160
    for cD in (Fraction(0),Fraction(1),Fraction(10**12),
               Fraction(10**30)):
        N=20
        while lower_subfamily(N) <= Mcore/2 + 4*cD:
            N*=2
        assert lower_subfamily(N)>Mcore/2+4*cD


def test_literal_four_moment_single_zero_row_increment():
    # Agda literal residual R_NC = nC*R_N+nN*R_C-rN*M_C-rC*M_N,
    # followed by negative coherent work. Replacing one zero-amplitude
    # noncore triad affects ONLY nN and rN; modal sums remain unchanged.
    def defect(nN,nC,rN,rC,vN,vC,wN,wC):
        return -(nC*wN+nN*wC-rN*vC-rC*vN)
    for (nN,nC,rN,rC,vN,vC,wN,wC,s) in (
        (1,3,5,7,Fraction(1,3),1,Fraction(3,7),2,10),
        (100,9,400,20,0,1,0,2,1024),
        (0,2,0,4,0,1,0,2,8),
    ):
        diff=(defect(nN+1,nC,rN+s,rC,vN,vC,wN,wC)
             -defect(nN,nC,rN,rC,vN,vC,wN,wC))
        assert diff==s*vC-wC
        if vC==1 and wC==2:
            assert diff==s-2


def test_existing_R681_cross_gradient_is_zero_padding_invariant():
    # Existing Agda R681 theorem, *not* a newly proposed identity:
    # r_pq=|p|²+|q|²=|k|²-2(p·q), on each literal p+q=k.
    # For any signed coherent cell-work weights w, this produces the
    # source-equivalent raw weighted physical R440 aggregate.
    from fractions import Fraction as F
    rows=[
        ((1,0,0),(0,1,0),F(1,2)),
        ((2,0,1),(-1,1,-1),F(-3,7)),
        ((-4,1,0),(5,0,0),F(11,9)),
    ]
    k=module.K
    for p,q,w in rows:
        assert tuple(p[j]+q[j] for j in range(3)) == k
        input_rate=sum(x*x for x in p)+sum(x*x for x in q)
        output_rate=sum(x*x for x in k)
        dot=sum(p[j]*q[j] for j in range(3))
        assert input_rate == output_rate-2*dot
        assert input_rate*w == output_rate*w-2*dot*w

    def signed_normal_form(triads):
        raw=sum((sum(x*x for x in p)+sum(x*x for x in q))*w
                for p,q,w in triads)
        weighted_output=sum(x*x for x in k)*sum(w for _,_,w in triads)
        cross=-2*sum(sum(p[j]*q[j] for j in range(3))*w
                     for p,q,w in triads)
        assert raw==weighted_output+cross
        return raw
    before=signed_normal_form(rows)
    # Zero amplitudes with arbitrarily large input rates never alter
    # this genuine physical rate/heat source, unlike full-fibre centering.
    for m in (10,100,1000):
        p=(m,0,0)
        q=(1-m,1,0)
        assert signed_normal_form(rows+[(p,q,F(0))])==before


def test_R681_is_not_the_old_B4_defect_same_output_shear():
    # On the SAME smooth physical shear and output:
    # R681 weighted physical input-rate work = 2,
    # |k|²*W(M,M) = 2, cross-gradient = 0.
    # The deprecated full-fibre B4 signed noncore/core defect is
    # 185520 at N9 and 1671172320 at N40.
    # Therefore direct equality of R681's PAD-INVARIANT physical
    # output-relative work with the old B4 defect is FALSE.
    # An admissible repair must use a compensated global recombination
    # over all physical classes/outputs, not merely rename B4.
    output_heat_relative=Fraction(0)
    for n in (9,16,40):
        assert Fraction(module.certificate(n)["signed_defect"]) > 0
        assert Fraction(module.certificate(n)["signed_defect"]) != output_heat_relative
    assert output_heat_relative==(
        Fraction(2)-Fraction(sum(x*x for x in module.K))*Fraction(1))
