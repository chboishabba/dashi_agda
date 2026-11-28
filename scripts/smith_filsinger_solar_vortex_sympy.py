"""DASHI model extension; Gong et al. DOI 10.1051/0004-6361/202661571
is the simulation donor, not an Earth receiver measurement.
Run from scripts/ with the existing local ADE owner available.
"""
import sympy as S


def axial_flux(B, v, mu, R=(0, 0, 0)):
    """Cylindrical orthonormal components; R=E+v cross B (nonideal E)."""
    B, v, R = map(lambda x: S.Matrix(x), (B, v, R))
    mu = S.sympify(mu)
    if mu.is_positive is not True:
        raise ValueError('positive permeability required')
    if any(x.shape != (3, 1) for x in (B, v, R)):
        raise ValueError('three components required')
    br, bp, bz = B
    vr, vp, vz = v
    rr, rp, _ = R
    terms = ((br**2+bp**2)*vz/mu, -bz*br*vr/mu,
             -bz*bp*vp/mu, (rr*bp-rp*br)/mu)
    total = S.factor(sum(terms))
    assert S.simplify(total - ((-v.cross(B)+R).cross(B))[2]/mu) == 0
    return tuple(map(S.factor, terms)), total


def reverse_twist(B, vr, vz, mu, target, R=(0, 0, 0)):
    """Exact affine inverse; retain zero-slope nonidentifiability."""
    p = S.Dummy('vphi', real=True)
    _, flux = axial_flux(B, (vr, p, vz), mu, R)
    slope = S.diff(flux, p)
    intercept = flux.subs(p, 0)
    residual = S.simplify(S.sympify(target)-intercept)
    if slope.is_zero is True:
        return ('all' if residual.is_zero is True else
                'none' if residual.is_zero is False else 'undecided', None)
    if slope.is_zero is not False:
        return 'undecided', None
    return 'unique', S.cancel(residual/slope)


def integrated_work(samples):
    """Signed face quadrature, exact for supplied piecewise constant samples.
    Each tuple is (original face ID, time index, outward signed flux, area, dt).
    Not an inferred integral of the published mean without area/time support.
    """
    seen, work = set(), S.S.Zero
    for face, time, flux, area, dt in samples:
        key = (face, time)
        if key in seen:
            raise ValueError('duplicate face/time')
        seen.add(key)
        flux, area, dt = map(S.sympify, (flux, area, dt))
        if area.is_positive is not True or dt.is_positive is not True:
            raise ValueError('positive area and duration required')
        work += flux*area*dt
    return S.factor(work)


def receiver_cap(source_work, efficiencies):
    """Conditional passive serial bound, never a measured Earth source."""
    w = S.sympify(source_work)
    if w.is_nonnegative is not True:
        raise ValueError('nonnegative admitted incident work required')
    for eta in map(S.sympify, efficiencies):
        if eta.is_nonnegative is not True or (1-eta).is_nonnegative is not True:
            raise ValueError('passive efficiency in [0,1] required')
        w *= eta
    return S.factor(w)


def weld_paid_kick(spec, z, cell, current, dt, admitted_work):
    """Use existing owner; source injection is conditional on paid incident work.
    A positive flux is not itself a current or authenticated natural source.
    """
    from smith_filsinger_local_causal_ade_sympy import source_kick
    budget = S.sympify(admitted_work)
    if budget.is_nonnegative is not True:
        raise ValueError('nonnegative source budget required')
    record = source_kick(spec, z, cell, current, dt, origin='natural')
    work = record['work']
    if work.is_nonnegative is not True or (budget-work).is_nonnegative is not True:
        raise ValueError('kick exceeds or reverses admitted source work')
    return dict(record=record, unused_budget=S.factor(budget-work),
                physical_source_meter=False, terrestrial_coupling_verified=False)


def self_test():
    br, bp, bz, vr, vp, vz, rr, rp, rz = S.symbols('br bp bz vr vp vz rr rp rz', real=True)
    mu = S.symbols('mu', positive=True)
    _, f = axial_flux((br,bp,bz),(vr,vp,vz),mu,(rr,rp,rz))
    assert S.diff(f,vp) == -bp*bz/mu
    assert axial_flux((0,2,3),(0,-4,0),1)[1] == 24
    assert axial_flux((0,2,3),(0,4,0),1)[1] == -24
    assert axial_flux((0,-2,-3),(0,-4,0),1)[1] == 24
    assert axial_flux((0,2,0),(0,-4,0),1)[1] == 0
    assert axial_flux((0,2,3),(0,0,0),1,(3,0,0))[1] == 6
    assert reverse_twist((0,2,3),0,0,1,24) == ('unique',-4)
    assert reverse_twist((0,2,0),0,0,1,0) == ('all',None)
    assert reverse_twist((0,2,0),0,0,1,1) == ('none',None)
    assert integrated_work([('a',0,3,2,1),('b',0,-2,2,1)]) == 2
    assert receiver_cap(100,(S.Rational(1,2),S.Rational(1,5),0)) == 0
    assert receiver_cap(100,(S.Rational(1,2),S.Rational(1,5))) == 10
    for fn,args in [(integrated_work,([('a',0,3,2,1),('a',0,3,2,1)],)),
                    (receiver_cap,(100,(2,))), (receiver_cap,(-1,(1,)))]:
        try:
            fn(*args)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid source accepted')
    print('15 exact symbolic/fixture controls passed; ADE integration requires donor modules')


if __name__ == '__main__':
    self_test()
