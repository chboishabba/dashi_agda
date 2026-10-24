"""DASHI-original exact unforced Beltrami heat shear and T3 audit.

Prior art: classical Beltrami/curl eigenflow, not our discovery.
Source-specific candidate: Permana--Ibrahim--Lathif Zenodo v3
19632058 (17 April 2026), proposed T3=||curl(omega x u)||².
This demonstrates T3 is non-coercive with respect to vorticity
direction curvature and enstrophy without further hypotheses.
It does NOT falsify their T3-weighted alignment inequality on
this very field: the alignment also vanishes.
"""
import sympy as s

def datum(n):
    x,t,A,nu=s.symbols('x t A nu',positive=True,real=True)
    factor=A/s.Integer(n)*s.exp(-nu*n*n*t)
    u=s.Matrix([0,factor*s.sin(n*x),factor*s.cos(n*x)])
    omega=s.Matrix([0,-s.diff(u[2],x),s.diff(u[1],x)])
    return (x,t,A,nu),u,omega

def test_exact_beltrami_and_unforced_heat():
    for n in (1,2,7,19):
        (x,t,A,nu),u,w=datum(n)
        assert s.simplify(w-n*u)==s.zeros(3,1)
        assert s.simplify(w.cross(u))==s.zeros(3,1)
        assert s.simplify(s.diff(u,t)-nu*s.diff(u,x,2))==s.zeros(3,1)
        # u has only y/z components, depends only on x:
        # (u.grad)u=0; the pressure can be constant.
        assert u[0]==0

def test_T3_zero_with_high_direction_curvature():
    for n in (2,3,8,23):
        (x,t,A,nu),u,w=datum(n)
        lamb=w.cross(u)
        curl_lamb=s.Matrix([0,-s.diff(lamb[2],x),s.diff(lamb[1],x)])
        assert s.simplify(curl_lamb)==s.zeros(3,1)
        assert s.simplify((curl_lamb.T*curl_lamb)[0])==0
        direction=s.Matrix([0,s.sin(n*x),s.cos(n*x)])
        assert s.simplify(w-A*s.exp(-nu*n*n*t)*direction)==s.zeros(3,1)
        assert s.simplify((s.diff(direction,x).T*s.diff(direction,x))[0]-n*n)==0
        assert s.simplify((w.T*w)[0]-A*A*s.exp(-2*nu*n*n*t))==0

def test_T3_plus_kinetic_energy_does_not_coerce_enstrophy():
    n,A,nu=s.symbols('n A nu',positive=True)
    tn=1/(nu*n*n)
    E=A*A*s.exp(-2*nu*n*n*tn)/(n*n)
    D=A*A*s.exp(-2*nu*n*n*tn)
    helicity=A*A*s.exp(-2*nu*n*n*tn)/n
    assert s.simplify(D-A*A*s.exp(-2))==0
    assert s.limit(E,n,s.oo)==0
    assert s.limit(helicity,n,s.oo)==0
    assert s.limit(n/s.sqrt(A*s.exp(-1)),n,s.oo)==s.oo
    # Since T3=0 for ALL n: D/(E+T3)=n² -> infinity.
    assert s.simplify(D/E)==n*n

def test_alignment_is_zero_so_claimed_T3_alignment_not_refuted():
    for n in (2,5,11):
        (x,t,A,nu),u,w=datum(n)
        xi=s.Matrix([0,s.sin(n*x),s.cos(n*x)])
        grad=s.Matrix([[0,0,0],[s.diff(u[1],x),0,0],[s.diff(u[2],x),0,0]])
        strain=(grad+grad.T)/2
        assert s.simplify(strain*xi)==s.zeros(3,1)
        assert s.simplify((xi.T*strain*xi)[0])==0
        assert s.simplify(s.diff(xi,x,2)+n*n*xi)==s.zeros(3,1)

def test_T3_zero_does_not_control_velocity_H2_or_directional_curvature():
    # The author-uploaded v4 manuscript, Remark 3.7, appeals to an
    # elliptic H2 control from T3. Beltrami flows lie in J's kernel.
    # On the normalized periodic torus at t=1/(nu*n²):
    # ||Delta u||² = A² n²/e², ||omega||²=A²/e²,
    # T3=0, ||grad xi||∞=n.
    for n in (2,5,20,100):
        (x,t,A,nu),u,w=datum(n)
        t_n=1/(nu*n*n)
        lap_u=s.diff(u,x,2)
        lap_sq=s.simplify((lap_u.T*lap_u)[0])
        assert s.simplify(
            lap_sq.subs(t,t_n)-A*A*n*n*s.exp(-2))==0
        assert s.simplify((w.T*w)[0].subs(t,t_n)-A*A*s.exp(-2))==0
        assert s.simplify(w.cross(u))==s.zeros(3,1)
    # Therefore no finite multiplier C can ensure
    # ||u||_dotH²² <= C*T3 for all smooth divergence-free u.
