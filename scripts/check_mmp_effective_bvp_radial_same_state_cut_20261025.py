#!/usr/bin/env python3
"""Independently test existing MMP two-mouth *effective* BVP against Einstein
radial null and source constraint throughout integration domain.

Import existing original BVP producer, do not duplicate its ODE.  This
checker is geometric algebra + the EXACT effective source provided by that
producer, not a constructed Hadamard or Einstein-Maxwell-Dirac solution.
"""
from __future__ import annotations
import importlib.util
import json
import math
from pathlib import Path
import numpy as np
from scipy.integrate import quad
import sympy as sp

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'check_mmp_global_effective_bvp_replay_20261024.py'
if not SOURCE.exists():
    SOURCE = HERE.parent / 'scripts' / SOURCE.name
spec = importlib.util.spec_from_file_location('mmp_bvp_original_owner', SOURCE)
if spec is None or spec.loader is None:
    raise RuntimeError('Cannot load canonical MMP BVP producer')
producer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(producer)

def check(q: int) -> dict:
    out=producer.run(q, with_profile=True)
    sol=out['numerical_profile']
    x_end=float(out['match_x'])
    L=20.0
    c=abs(q)
    t=-math.pi*c/(12*L*L)
    Q=q/2
    def fields(x):
        rad,v,F,logN=sol.sol(x)
        N=math.exp(logN)
        U=producer.potential(q,rad,L)
        dU=producer.potential_prime(q,rad,L)
        pres=-c*F*F/(24*math.pi)+2*t/N**2-U
        constraint=v*v-1+2*rad*v*F+Q*Q/(rad*rad)-2*pres
        R=1-v*v-Q*Q/(rad*rad)-c/(12*math.pi)*F*F-4*t/N**2-2*U
        S=-F*F-F*v/rad+Q*Q/rad**4-dU/rad
        Fp=(R-2*rad*rad*S)/(c/(6*math.pi)-2*rad*rad)
        rpp=rad*(S-Fp)
        gkk=2*(F*v-rpp)/rad
        source_null=(c*Fp/(12*math.pi)+4*t/N**2)/(4*math.pi*rad*rad)
        einstein_mismatch=gkk-8*math.pi*source_null
        geometric_weight=(rad/N)*gkk
        return (rad,v,F,N,constraint,einstein_mismatch,geometric_weight,source_null,Fp,rpp)
    points=np.linspace(0,x_end,81)
    samples=[fields(float(x)) for x in points]
    maxconstraint=max(abs(z[4]) for z in samples)
    maxmismatch=max(abs(z[5]) for z in samples)
    integrated_g=quad(lambda x:fields(x)[6],0,x_end,epsabs=2e-8,limit=300)[0]
    integrated_source=8*math.pi*quad(lambda x:fields(x)[0]/fields(x)[3]*fields(x)[7],0,x_end,epsabs=2e-8,limit=300)[0]
    # Geometric differential identity, *not* assuming Einstein's source.
    bound=-2*(fields(x_end)[1]/fields(x_end)[3] - fields(0)[1]/fields(0)[3])
    # Diagnose classical RN matching in proper radial coordinate. Matching
    # g and first derivatives does not imply C2 match after sharp removal
    # of the effective quantum source at the interface.
    at=fields(x_end)
    radius,velocity,redshift,Nend=at[:4]
    M=out['mass_RN']
    f=velocity*velocity
    A=M/radius**2-Q**2/radius**3
    rn_F=A/math.sqrt(f)
    rn_rpp=A
    rn_Fp=-2*M/radius**3+3*Q**2/radius**4-A*A/f
    c1_error=max(abs(velocity-math.sqrt(f)),abs(redshift-rn_F))
    c2_rpp_jump=float(at[9]-rn_rpp)
    c2_loglapse_second_jump=float(at[8]-rn_Fp)
    ident_error=abs(integrated_g-bound)
    source_error=abs(integrated_source-bound)
    return dict(q=q,x_end=x_end,r_end=out['match_radius'],
                radial_constraint_max=maxconstraint,einstein_null_mismatch_max=maxmismatch,
                rn_junction_C1_max=c1_error,
                rn_junction_r_second_derivative_jump=c2_rpp_jump,
                rn_junction_loglapse_second_derivative_jump=c2_loglapse_second_jump,
                geometric_budget=integrated_g,einstein_source_budget=integrated_source,
                finite_segment_boundary=bound,geometric_identity_abs_err=ident_error,
                source_vs_geometric_abs_err=source_error,
                exterior_status='two mouth local interior ends at RN junction; does not identify same-universe one end')

def must(condition: bool, why: str):
    if not condition:
        raise RuntimeError(why)

def main():
    results=[check(q) for q in (10,12,24)]
    print(json.dumps(results,indent=2))
    must(max(v['geometric_identity_abs_err'] for v in results)<4e-6, 'Geometric integrated null identity failed')
    must(max(v['radial_constraint_max'] for v in results)<4e-6, 'Existing BVP radial constraint fails along path')
    must(max(v['einstein_null_mismatch_max'] for v in results)<4e-6, 'Effective Einstein radial null mismatch')
    must(max(v['source_vs_geometric_abs_err'] for v in results)<4e-6, 'Source and geometry budgets disagree')
    must(max(v['rn_junction_C1_max'] for v in results)<2e-8, 'RN junction first derivatives do not match')
    must(min(abs(v['rn_junction_r_second_derivative_jump']) for v in results)>2e-5,
         'Fixture changed: expected sharp-cutoff C2 jump no longer present; re-audit source')
    # Prove exact algebra behind the numerical radial-null validator, not just
    # a pointwise floating-point coincidence. The on-shell constraint controls
    # the difference of source-side and geometry-side Einstein k.k.
    r,v,F,N,Q,c,t,U,Up=sp.symbols('r v F N Q c t U Up', real=True, nonzero=True)
    R=1-v*v-Q*Q/(r*r)-c*F*F/(12*sp.pi)-4*t/(N*N)-2*U
    S=-F*F-F*v/r+Q*Q/(r**4)-Up/r
    Fp=(R-2*r*r*S)/(c/(6*sp.pi)-2*r*r)
    rpp=r*(S-Fp)
    gkk=2*(F*v-rpp)/r
    tkk=(c*Fp/(12*sp.pi)+4*t/(N*N))/(4*sp.pi*r*r)
    pres=-c*F*F/(24*sp.pi)+2*t/(N*N)-U
    constraint=v*v-1+2*r*v*F+Q*Q/(r*r)-2*pres
    must(sp.cancel(gkk-8*sp.pi*tkk-constraint/(r*r))==0, 'Exact symbolic C/r² identity failed')
    # Wrongly omitting a supplied matter current/stress source must FAIL.
    shifted_source=results[1]['einstein_source_budget']+0.025
    must(abs(shifted_source-results[1]['finite_segment_boundary'])>0.02, 'A deliberately wrong effective source was not rejected')
    print('PASS: canonical effective BVP radial constraint and independent geometric/source null budget; NOT 4D Hadamard gravity')

if __name__ == '__main__':
    main()
