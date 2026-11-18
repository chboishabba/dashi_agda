#!/usr/bin/env python3
"""P3 diamond MCG finite-array geometry/resource controls.

Synthetic mathematical model only; no calibrated NV or human-heart data.
Magnetic dipole tensor with 3 unknown source moment coordinates. Uses
Woodbury to evaluate GLS Gram under diagonal + positive low-rank ambient noise.
Compares fixed per-channel sensitivity with fixed aggregate readout budget.
"""
import json
import numpy as np
import sympy as sp


def exact_checks():
    r,h,v,c=sp.symbols('r h v c', positive=True)
    # Fixed total resource: n sensors independent variance n*v -> information fixed.
    for n in (1,2,3,10):
        info=sp.Rational(n,1)/(n*v)
        assert sp.simplify(info-1/v)==0
    # Signal-to-noise optimality with a low-rank nuisance and exact Woodbury.
    D=sp.diag(2,3)
    U=sp.Matrix([[1],[2]])
    identity=sp.eye(2)
    C=D+U*U.T
    inverse=D.inv()-D.inv()*U*(sp.eye(1)+U.T*D.inv()*U).inv()*U.T*D.inv()
    assert (C*inverse-identity).applyfunc(sp.cancel)==sp.zeros(2)
    # Dipole geometry: transverse moment null on axial z measurement.
    A=sp.diag(-r**-3,-r**-3,2*r**-3)
    assert A[2,0]==0 and A[2,1]==0 and A[2,2]==2/r**3
    # Schur complement of one sensor in a correlated pair.
    C2=sp.Matrix([[v,c],[c,v]])
    det=sp.factor(C2.det())
    assert sp.factor(det-(v-c)*(v+c))==0
    return True


def positions(n,width):
    k=np.arange(n,dtype=float)
    # Deterministic disk fill avoids an unfair regular-grid alignment.
    radius=(width/2)*np.sqrt((k+0.5)/n)
    theta=k*np.pi*(3-np.sqrt(5))
    return np.column_stack((radius*np.cos(theta),radius*np.sin(theta),np.zeros(n)))


def design(n,width,orientation):
    pos=positions(n,width)
    axes=np.zeros((n,3))
    if orientation=='single-z': axes[:,2]=1.0
    elif orientation=='tri-axial': axes[np.arange(n),np.arange(n)%3]=1.0
    else:raise ValueError(orientation)
    return pos,axes


def response(pos,axes,range_m):
    direction=np.array([0.,0.,range_m])[None,:]-pos
    dist=np.linalg.norm(direction,axis=1)
    unit=direction/dist[:,None]
    # Sensor-axis projection of the 3-vector magnetic dipole moment response.
    # B/(mu0 m_ref / 4pi) has units 1/m^3; evaluate r_ref=1m normalization.
    return (3*np.sum(axes*unit,axis=1)[:,None]*unit-axes)/dist[:,None]**3


def information(pos,axes,range_m,resource_mode,ambient_std=0.5,gradient_std=0.15):
    n=len(pos)
    S=response(pos,axes,range_m)
    # Independent-channel noise variance increases with N if total optical
    # photon/measurement budget is fixed. Alternative per-channel budget is
    # deliberately NOT equal-resources.
    noise_var=float(n if resource_mode=='fixed-total' else 1.)
    # Ambient 3-vector common magnetic field plus two simple 3D gradients.
    # All nuisance magnitudes are dimensionless illustrative ratios to
    # single-channel baseline noise, not data-derived covariance.
    U=[ambient_std*axes[:,j] for j in range(3)]
    for j in (0,1):
        U.extend([gradient_std*axes[:,k]*pos[:,j] for k in range(3)])
    U=np.array(U).T
    invD_S=S/noise_var
    invD_U=U/noise_var
    tmp=np.eye(U.shape[1])+U.T@invD_U
    # Stable GLS Gram from Woodbury; no 1000x1000 matrix inversion.
    gram=S.T@invD_S-(S.T@invD_U)@np.linalg.solve(tmp,U.T@invD_S)
    gram=(gram+gram.T)/2
    eig=np.linalg.eigvalsh(gram)
    if np.min(eig)<-1e-12:raise AssertionError('PSD failure')
    return {'trace':float(np.trace(gram)),
            'worst_orientation':float(max(0.,eig[0])),
            'best_orientation':float(eig[-1]),
            'eigenvalues':[float(v) for v in eig]}


def run():
    exact_checks()
    rows=[]
    for n in (1,100,1000):
      for width in (0.02,0.50):
       for orientation in ('single-z','tri-axial'):
        for resource in ('fixed-total','per-channel'):
         pos,axes=design(n,width,orientation)
         for distance in (2.,10.,100.,1000.):
          metric=information(pos,axes,distance,resource)
          rows.append({'n':n,'width_m':width,'axes':orientation,
                       'budget':resource,'range_m':distance,**metric})
    # Regression: no multi-axis near-coincident geometry can reconstruct 3
    # components if every sensor is exactly co-located and measures z only.
    co_pos=np.zeros((100,3));co_axes=np.tile([0.,0.,1.],(100,1))
    assert information(co_pos,co_axes,10.,'fixed-total')['worst_orientation']==0
    # Check fixed-total equivalence for all-coincident aligned sensors with
    # no shared interference: independent noise N gives the same information.
    for n in (1,100,1000):
        pos=np.zeros((n,3));axes=np.tile([0.,0.,1.],(n,1))
        info=information(pos,axes,10.,'fixed-total',ambient_std=0,gradient_std=0)
        assert abs(info['trace']-4e-6)<1e-16,(n,info)
    # Triple-axis array resolves the entire vector source at short distance.
    pos,axes=design(100,0.02,'tri-axial')
    assert information(pos,axes,10.,'fixed-total')['worst_orientation']>0
    # More sensors with per-channel independent resources should produce
    # larger information for coincident, common orientation and zero ambient.
    def rank1(n):
        return information(np.zeros((n,3)),np.tile([0.,0.,1.],(n,1)),
                           10.,'per-channel',ambient_std=0,gradient_std=0)['trace']
    assert abs(rank1(1000)/rank1(100)-10)<1e-10
    print('PASS: exact Woodbury, resource normalization, rank-one orientation null, 100/1000 regression')
    for row in rows:
        if row['range_m']==10 and row['budget']=='fixed-total' and row['n'] in (100,1000):
            print('DESIGN',row['n'],row['width_m'],row['axes'],
                  'trace',f"{row['trace']:.5e}",
                  'worst',f"{row['worst_orientation']:.5e}")
    print('OPEN: measured noise, optical readout scaling, full cardiac current/tissue model, phase and false alarm')
    return {'schema':'diamond-mcg-P3-synthetic-v1',
            'measured_data':False,'physical_validation':False,
            'assumptions':{'reference_range_m':1,
                           'dipole':'static point moment, all orientations assessed',
                           'noise':'diagonal + three-vector uniform ambient + six gradient modes',
                           'fixed_total_channel_variance': 'N times a one-channel reference variance',
                           'ambient_std':0.5,'gradient_std':0.15,
                           'distance_units':'metre',
                           'array_width':'disk diameter'},'rows':rows}


if __name__=='__main__':
    out=run()
    with open('diamond_array_p3_results.json','w') as f:
        json.dump(out,f,indent=2)
