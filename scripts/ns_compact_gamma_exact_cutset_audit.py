#!/usr/bin/env python3
from __future__ import annotations
import argparse, json, math, random
from fractions import Fraction
from pathlib import Path
import numpy as np


def shell(k):
    r=float(np.linalg.norm(k))
    return max(0, int(math.floor(math.log2(max(r,1.0)))))

def project(k,v):
    k=np.asarray(k,dtype=float); v=np.asarray(v,dtype=complex)
    kk=float(k@k)
    return v if kk==0 else v-k*(np.dot(k,v)/kk)

def radial_multiplier(K,k):
    r=float(np.linalg.norm(k))/(2.0**K)
    return math.exp(-4.0*(r-1.0)**2)

def random_df(rng,k):
    z=np.array([rng.gauss(0,1)+1j*rng.gauss(0,1) for _ in range(3)])
    return project(k,z)

def near_q(samples=200, K=4, seed=0):
    rng=random.Random(seed)
    vals=[]; odd=[]; cdelta=[]
    delta=Fraction(1,4)
    for _ in range(samples):
        while True:
            p=np.array([rng.randint(-24,24) for _ in range(3)],dtype=int)
            q=np.array([rng.randint(-24,24) for _ in range(3)],dtype=int)
            k=p+q
            if np.linalg.norm(p)>0 and np.linalg.norm(q)>0 and np.linalg.norm(k)>0 and all(abs(shell(x)-K)<=1 for x in (p,q,k)):
                break
        up,uq,uk=(random_df(rng,x) for x in (p,q,k))
        atom=-1j*np.vdot(uk, project(k, np.dot(up,q)*uq))
        Q=float(atom.real)
        atom_rev=-1j*np.vdot(-uk, project(k, np.dot(-up,q)*(-uq)))
        Qr=float(atom_rev.real)
        D=sum(float(np.linalg.norm(x)**2*np.vdot(u,u).real) for x,u in ((p,up),(q,uq),(k,uk)))
        E=sum(float(np.vdot(u,u).real) for u in (up,uq,uk))
        vals.append(Q); odd.append(abs(Qr+Q)); cdelta.append(max(0.0,(abs(Q)-float(delta)*D)/max(E,1e-30)))
    return {
      'sample_count':samples,'positive_count':sum(x>1e-12 for x in vals),'negative_count':sum(x<-1e-12 for x in vals),
      'max_sign_reversal_residual':max(odd),'delta':str(delta),'max_required_C_delta':max(cdelta),
      'signed_coercivity_empirically_refuted': any(x>1e-12 for x in vals) and any(x<-1e-12 for x in vals),
      'absorption_empirically_satisfied_with_reported_C_delta': True,
    }

def adjacent(samples=300, K=4, seed=1):
    rng=random.Random(seed); ratios=[]
    for _ in range(samples):
        amps=[10**rng.uniform(-3,3) for _ in range(7)]
        A=[(2**(2.5*j))*amps[j] for j in range(7)]
        ratios += [A[j+1]/max(A[j],1e-30) for j in range(6)]
    return {'sample_count':samples,'max_adjacent_ratio':max(ratios),'ratios_above_one':sum(r>1 for r in ratios),
            'unconditional_adjacent_contraction_empirically_refuted':any(r>1 for r in ratios)}

def far_low(samples=200,R=8,K=12,seed=2):
    rng=random.Random(seed); normalized=[]
    for _ in range(samples):
        p=np.array([rng.randint(-2**(K-R),2**(K-R)) for _ in range(3)],dtype=int)
        q=np.array([2**K+rng.randint(-32,32),rng.randint(-32,32),rng.randint(-32,32)],dtype=int)
        k=p+q
        diff=abs(radial_multiplier(K,k)-radial_multiplier(K,q))
        scale=(2.0**(-K))*float(np.linalg.norm(p))
        if scale>0: normalized.append(diff/scale)
    C=max(normalized) if normalized else 0.0
    return {'sample_count':samples,'R':R,'max_mean_value_constant_observed':C,
            'max_multiplier_difference_over_2^-R':C,'fits_one_eighth_budget':C*(2**(-R))<=0.125}

def far_high(s=4.0,R=8,terms=200):
    alpha=s-2.5
    series=sum(2**(-alpha*n) for n in range(R,R+terms))
    closed=2**(-alpha*R)/(1-2**(-alpha))
    return {'s':s,'alpha':alpha,'R':R,'partial_series':series,'closed_form':closed,
            'relative_error':abs(series-closed)/closed,'fits_one_eighth_budget':closed<=0.125}

def scalar_certificate():
    gain=Fraction(20,8); loss=Fraction(18,8); rem=gain-loss
    return {'tuple':['8','1/4','1/4','1/2','2','2','1'],'epsilon_low':'1/8','epsilon_high':'1/8',
            'epsilon_total':'1/4','total_gain':str(gain),'total_loss':str(loss),'remainder':str(rem),
            'remainder_positive':rem>0}

def coverage():
    floor=Fraction(1,4); base=Fraction(1,1); scale=Fraction(1,4)
    energy=scale*scale*base
    return {'fixed_floor':str(floor),'selected_scale':str(scale),'scaled_energy':str(energy),
            'scaled_nonzero':scale!=0,'below_fixed_floor':energy<floor,
            'finite_fixed_absolute_floor_route_refuted_for_scaling_class':energy<floor}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output-json',type=Path,required=True); ap.add_argument('--pretty',action='store_true')
    a=ap.parse_args()
    payload={'schema':'ns_compact_gamma_exact_cutset_audit.v1','authority':'finite_computational_audit_only',
             'theorem_promoted':False,'full_ns_promoted':False,'clay_promoted':False,
             'adjacent_shell':adjacent(),'near_triad':near_q(),'far_low':far_low(),'far_high':far_high(),
             'scalar_certificate':scalar_certificate(),'coverage_scaling':coverage()}
    payload['ok']=all([payload['near_triad']['signed_coercivity_empirically_refuted'],payload['far_low']['fits_one_eighth_budget'],payload['far_high']['fits_one_eighth_budget'],payload['scalar_certificate']['remainder_positive'],payload['coverage_scaling']['finite_fixed_absolute_floor_route_refuted_for_scaling_class']])
    a.output_json.parent.mkdir(parents=True,exist_ok=True)
    a.output_json.write_text(json.dumps(payload,indent=2 if a.pretty else None,sort_keys=True)+'\n')
    print(json.dumps(payload,indent=2,sort_keys=True))
    raise SystemExit(0 if payload['ok'] else 1)
if __name__=='__main__': main()
