#!/usr/bin/env python3
"""S4c.5: exact graph codec and numerical accepted backward-Euler replay."""
import json
import numpy as np
from sympy import Matrix, eye, zeros, __version__
from reactive_pnp_369 import (POINTS, BONDS, INDEX, Model, implicit_step,
                              poisson, native_flux, reaction_rates)


def codec():
    B=zeros(len(POINTS),len(BONDS))
    for j,(a,b) in enumerate(BONDS):
        B[a,j],B[b,j]=-1,1
    A=B[:26,:]
    K=A.T*(A*A.T).inv(method='DM')
    P=eye(54)-K*A
    Z=Matrix.hstack(*A.nullspace())
    chords=[j for j in range(54) if j not in A.rref()[1]]
    G=eye(54)[chords,:]
    assert G*Z==eye(28) and Z*G*P==P
    assert A*K==eye(26) and A*Z==zeros(26,28)
    assert K*A+Z*G*P==eye(54)
    return [np.array(x.tolist(),dtype=float) for x in (A,K,Z,G*P)]


def run_case(name, m, c0, dts, ops):
    A,K,Z,H=ops
    c=c0.copy(); ns=len(m.z)
    div=np.zeros((26,ns)); cycles=np.zeros((28,ns))
    full=np.zeros((54,ns))  # validation only; not part of codec state
    budget=0.; max_step=0.; max_poisson=0.; min_c=float(c.min())
    max_cycle=0.; reaction_sum=np.zeros_like(c)
    for dt in dts:
        nxt,receipt=implicit_step(c,dt,m,rtol=1e-8)
        phi=poisson(nxt,m)
        # Backward Euler: same accepted endpoint for flux and reaction.
        j=dt*m.h**2*native_flux(nxt,phi,m)
        rx=dt*m.h**3*(reaction_rates(nxt,m)@(m.products-m.reactants))
        corrected=m.h**3*(nxt-c)-rx
        d=corrected[:26,:]
        div+=d; cycles+=H@j; full+=j; reaction_sum+=rx
        budget+=m.h**3*receipt['numerical_residual_max']
        max_step=max(max_step,receipt['numerical_residual_max'])
        max_poisson=max(max_poisson,receipt['poisson_residual_max'])
        min_c=min(min_c,receipt['minimum_concentration'])
        max_cycle=max(max_cycle,float(np.max(np.abs(H@j))))
        assert receipt['free_energy_after']<=receipt['free_energy_before']+1e-8
        assert receipt['minimum_concentration']>0
        c=nxt
    decoded=K@div+Z@cycles
    err=float(np.max(np.abs(decoded-full)))
    # Solver defect bound, plus explicit numerical roundoff allowance (not interval certified).
    bound=float(np.linalg.norm(K,ord=np.inf)*budget)
    assert err<=bound+1e-11*max(1.,float(np.max(np.abs(full))))
    assert np.max(np.abs(div-(m.h**3*(c-c0)-reaction_sum)[:26]))<1e-10
    return dict(case=name,steps=len(dts),max_step_residual=max_step,
                max_poisson_residual=max_poisson,minimum_concentration=min_c,
                max_flux_error=err,solver_defect_bound=bound,
                max_stage_cycle=max_cycle,
                stock_only_error=float(np.max(np.abs(K@div-full))),
                omit_reaction_error=float(np.max(np.abs(K@(m.h**3*(c-c0)[:26])-full))),
                integrated_flux_max=float(np.max(np.abs(full))),
                codec_coordinates=54*ns,stored_trace_coordinates=54*ns*len(dts))


def check():
    ops=codec()
    out=[]
    for h in (0.7,1.0):
        for reactive in (False,True):
            m=Model(z=np.array([1.,-1.,0.]),D=np.array([.12,.1,.08]),
                reactants=np.array([[1,1,0]]) if reactive else np.empty((0,3),int),
                products=np.array([[0,0,1]]) if reactive else np.empty((0,3),int),
                kf=np.array([.04]) if reactive else np.empty(0),
                kb=np.array([.04]) if reactive else np.empty(0),standard_mu=np.zeros(3),h=h)
            c=np.tile([1.2,1.2,.4],(27,1))
            c[INDEX[(-1,0,0)],0]+=.4
            c[INDEX[(1,0,0)],1]+=.3
            c[INDEX[(0,-1,1)],0]+=.2
            result=run_case(f'h={h},reactive={reactive}',m,c,[.04,.08,.02,.06]*3,ops)
            assert result['stock_only_error']>1e-7
            if reactive:
                assert result['omit_reaction_error']>1e-4
            out.append(result)
    print(json.dumps({'sympy':__version__,'cases':out},indent=2,sort_keys=True))


if __name__=='__main__':
    check()
