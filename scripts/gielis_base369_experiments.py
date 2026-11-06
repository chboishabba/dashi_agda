#!/usr/bin/env python3
"""Gielis/Base369 finite Fourier, Dirichlet and open-spiral reflector diagnostics.

No PDE eigensolver or optical trace in this script is a continuum theorem.
The 18-sector rational identities, by contrast, use exact arithmetic.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import numpy as np

N = 18
CYCLES = {3:(2,1,-1,-2,-1,1), 6:(2,-1,-1), 9:(2,-2)}

def signature(m):
    """Exact 2*cos(2*pi*m*j/18), j=0,...,17."""
    if m not in CYCLES:
        raise ValueError("supported exact modes: 3, 6, 9")
    c = CYCLES[m]
    return tuple(c[j % len(c)] for j in range(N))

def projector(x, m):
    """C_m invariant averaging on the 18-sector common refinement."""
    if len(x) != N or N % m:
        raise ValueError("m must divide 18")
    step = N // m
    return tuple(sum((x[(j + k*step) % N] for k in range(m)), Fraction())/m
                 for j in range(N))

def exact_receipt():
    s = {m:signature(m) for m in CYCLES}
    gram = {f"{a}x{b}":sum(x*y for x,y in zip(s[a],s[b],strict=True))
            for a in CYCLES for b in CYCLES}
    assert gram == {"3x3":36,"3x6":0,"3x9":0,
                    "6x3":0,"6x6":36,"6x9":0,
                    "9x3":0,"9x6":0,"9x9":72}
    for m in CYCLES:
        assert all(s[m][(j+N//m)%N] == s[m][j] for j in range(N))
        assert all(s[m][(-j)%N] == s[m][j] for j in range(N))
    laws = ((6,9,18),(3,6,6),(3,9,9))
    # Each identity holds on all Q^18 by linearity once it holds
    # on its 18 standard basis vectors.
    for a,b,c in laws:
        for i in range(N):
            e = tuple(Fraction(j == i) for j in range(N))
            assert projector(projector(e,a),b) == projector(e,c)
            assert projector(projector(e,b),a) == projector(e,c)
    return {"gram":gram,"checked_basis_vectors":18,
            "projector_laws":[f"P{a}P{b}=P{c}" for a,b,c in laws],
            "number_system":"exact rational"}

def gielis_radius(theta, m, epsilon=1.0):
    """r=2/sqrt(3+epsilon*cos(m*theta)); epsilon=1 is Gielis exactly."""
    if abs(epsilon) >= 3:
        raise ValueError("positivity requires |epsilon|<3")
    return 2/np.sqrt(3+epsilon*np.cos(m*np.asarray(theta)))

def laplacian_eigenvalues(m, n=41, k=4):
    """Five-point Dirichlet approximation on a rasterized supershape domain."""
    from scipy.sparse import csr_matrix
    from scipy.sparse.linalg import eigsh
    if n < 17 or n % 2 != 1:
        raise ValueError("n must be odd and >= 17")
    axes = np.linspace(-1.5,1.5,n)
    h = axes[1]-axes[0]
    x,y = np.meshgrid(axes,axes,indexing="ij")
    inside = np.hypot(x,y) < gielis_radius(np.arctan2(y,x),m)-1e-12
    points = np.argwhere(inside)
    index = {tuple(p):j for j,p in enumerate(points)}
    row=[]; col=[]; data=[]
    for j,(i,t) in enumerate(points):
        row.append(j); col.append(j); data.append(4/h**2)
        for di,dt in ((1,0),(-1,0),(0,1),(0,-1)):
            neighbor = index.get((i+di,t+dt))
            if neighbor is not None:
                row.append(j);col.append(neighbor);data.append(-1/h**2)
    A = csr_matrix((data,(row,col)),shape=(len(points),len(points)))
    vals = np.sort(eigsh(A,k=k,which="SM",return_eigenvectors=False,tol=1e-8))
    assert np.all(vals > 0)
    return [float(v) for v in vals]

def spiral_vertices(m, epsilon, segments=1536):
    """Open 1.5-turn spiral: fixed 0.75m and 1.55m endpoint radii.

    A detrended log-Gielis modulation retains endpoint radii for every m.
    For epsilon=0 this is exactly the baseline logarithmic spiral.
    """
    if not (isinstance(m, int) and 1 <= m <= 27) or not (0 <= epsilon <= .45) or segments < 100:
        raise ValueError("invalid spiral parameters")
    T = 3*math.pi
    theta = np.linspace(0,T,segments+1)
    logbase = math.log(.75)+math.log(1.55/.75)*theta/T
    modulation = -.5*np.log((3+epsilon*np.cos(m*theta))/3)
    modulation -= modulation[0]+(modulation[-1]-modulation[0])*theta/T
    r = np.exp(logbase+modulation)
    assert abs(r[0]-.75)<1e-12 and abs(r[-1]-1.55)<1e-12
    return np.column_stack((r*np.cos(theta),r*np.sin(theta)))

def cross(a,b):
    return a[...,0]*b[...,1]-a[...,1]*b[...,0]

def nearest_hit(origin, direction, vertices):
    """Nearest ray/open-polyline intersection; returns (t,point,normal,index)."""
    a = vertices[:-1]; edge = vertices[1:]-a
    den = cross(np.broadcast_to(direction,edge.shape),edge)
    ok = np.abs(den)>1e-12
    delta = a-origin
    t = np.full(len(edge),np.inf)
    u = np.full(len(edge),np.inf)
    t[ok] = cross(delta[ok],edge[ok])/den[ok]
    u[ok] = cross(delta[ok],direction)/den[ok]
    admissible = (t>1e-7)&(u>=-1e-10)&(u<=1+1e-10)
    if not admissible.any():
        return None
    j = int(np.argmin(np.where(admissible,t,np.inf)))
    tangent = edge[j]/np.linalg.norm(edge[j])
    return float(t[j]),origin+t[j]*direction,np.array([-tangent[1],tangent[0]]),j

def circle_hit(origin,direction,center,radius):
    d = origin-center
    b = np.dot(d,direction)
    discriminant = b*b-(np.dot(d,d)-radius*radius)
    if discriminant < 0:
        return math.inf
    s = math.sqrt(discriminant)
    return min((float(t) for t in (-b-s,-b+s) if t>1e-7),default=math.inf)

def trace_ray(angle,vertices,max_bounces=8,absorber=True,outer_gate=1.70,
              record=False):
    """Specular reflections of a unit-speed ray; bounded collision count."""
    p = np.array([1.05,0.0])
    d = np.array([math.cos(angle),math.sin(angle)])
    origin = np.zeros(2)
    touched = False
    signed = 0.0; magnitude = 0.0
    path = [p.tolist()] if record else None
    collisions = [] if record else None
    if max_bounces < 0:
        raise ValueError("max_bounces must be nonnegative")
    exit_reason = "reflection_limit"
    reflections = 0
    # One free segment per reflection, one final propagation, and at most
    # one extra segment when an optional transparent target is crossed.
    for _ in range(max_bounces+3):
        hit = nearest_hit(p,d,vertices)
        surface_t = hit[0] if hit is not None else math.inf
        target_t = circle_hit(p,d,origin,.1) if not touched else math.inf
        gate_t = circle_hit(p,d,origin,outer_gate)
        if min(surface_t,target_t,gate_t) == math.inf:
            exit_reason="escaped_open_reflector"; break
        if target_t < min(surface_t,gate_t):
            touched=True
            if path is not None: path.append((p+target_t*d).tolist())
            if absorber:
                exit_reason="absorbed_at_target"; break
            p = p+(target_t+1e-6)*d
            continue
        if gate_t < surface_t:
            exit_reason="outer_gate"
            if path is not None: path.append((p+gate_t*d).tolist())
            break
        if hit is None:
            exit_reason="escaped_open_reflector"; break
        if reflections >= max_bounces:
            exit_reason = "reflection_limit"
            break
        _,point,normal,segment=hit
        new_d = d-2*np.dot(d,normal)*normal
        torque = float(cross(point,new_d-d))  # dimensionless momentum impulse
        signed+=torque; magnitude+=abs(torque)
        if collisions is not None:
            collisions.append({"point":point.tolist(),"segment":segment,"torque":torque})
        if path is not None: path.append(point.tolist())
        p=point+1e-6*new_d
        d=new_d/np.linalg.norm(new_d)
        reflections += 1
    return {"reflections":reflections,"hit_target":touched,"signed_torque":signed,"absolute_torque":magnitude,
            "exit_reason":exit_reason,"path":path,"collisions":collisions}

def optical_sweep(rays=720,segments=1536,bounces=8,absorber=True,include_controls=False):
    """Matched deterministic rays; not the legacy Kozyrev experiment."""
    angles = np.arange(rays)*2*math.pi/rays
    results=[]
    candidates = [(3,0.),(3,.12),(3,.24),(6,.12),(6,.24),(9,.12),(9,.24)]
    if include_controls:
        candidates.extend([(4,.12),(4,.24),(5,.12),(5,.24),(7,.12),(7,.24)])
    for m,eps in candidates:
        boundary = spiral_vertices(m,eps,segments)
        traces=[trace_ray(float(a),boundary,bounces,absorber) for a in angles]
        results.append({"m":m,"epsilon":eps,"rays":rays,"max_bounces":bounces,
                        "geometry":"endpoint_locked_open_1p5_turn_spiral",
                        "comparison_to_legacy":"not_same_apparatus",
                        "torque_unit":"unit_momentum_times_metre",
                        "model_code_bits":len(model_encode(m,eps)),
                        "total_reflections":sum(t["reflections"] for t in traces),
                        "focus_fraction":sum(t["hit_target"] for t in traces)/rays,
                        "mean_abs_torque":sum(t["absolute_torque"] for t in traces)/rays,
                        "mean_signed_torque":sum(t["signed_torque"] for t in traces)/rays,
                        "escapes":sum(t["exit_reason"] in ("outer_gate","escaped_open_reflector")
                                      for t in traces)})
    return results

def pareto(results, torque_objective="min"):
    """Nondominated designs, max focus, and min or max absolute impulse.

    Direction matters: 'min' treats impulse as a mechanical disturbance cost.
    'max' treats it as an intentionally delivered angular impulse benefit.
    """
    if torque_objective not in ("min", "max"):
        raise ValueError("torque_objective must be min or max")
    def dominates(b, a):
        fb,fa=b["focus_fraction"],a["focus_fraction"]
        tb,ta=b["mean_abs_torque"],a["mean_abs_torque"]
        torque_better=tb<=ta if torque_objective=="min" else tb>=ta
        torque_strict=tb<ta if torque_objective=="min" else tb>ta
        return fb>=fa and torque_better and (fb>fa or torque_strict)
    return [a for a in results if not any(dominates(b,a) for b in results)]

def elias_gamma_encode(n):
    """Prefix-free positive-integer code, not a Kolmogorov optimal code."""
    if not isinstance(n,int) or n <= 0:
        raise ValueError("gamma code accepts positive integers")
    b = format(n,"b")
    return "0"*(len(b)-1)+b

def elias_gamma_decode(bits,offset=0):
    if not isinstance(bits,str) or offset < 0 or offset >= len(bits):
        raise ValueError("invalid gamma payload")
    j = offset
    while j < len(bits) and bits[j] == "0":
        j += 1
    length = j-offset+1
    if j+length > len(bits) or any(ch not in "01" for ch in bits[offset:j+length]):
        raise ValueError("truncated/invalid gamma payload")
    return int(bits[j:j+length],2), j+length

def model_encode(m,epsilon):
    """Exact canonical *discrete* model code, epsilon in steps of 0.001.

    0 denotes the baseline logarithmic spiral (m irrelevant).
    1 gamma(m) gamma(1+round(1000*epsilon)) denotes modulated spirals.
    The encoding is prefix-free and explicitly reversible on admitted inputs.
    This upper-bounds description length in this codec; it is NOT true K(x).
    """
    if not isinstance(m,int) or not (1 <= m <= 27):
        raise ValueError("invalid integer mode")
    q = int(round(1000*epsilon))
    if not (0 <= q <= 450) or abs(epsilon-q/1000)>1e-12:
        raise ValueError("epsilon must be a nonnegative millistep <= .45")
    if q==0:
        return "0"
    return "1"+elias_gamma_encode(m)+elias_gamma_encode(q+1)

def model_decode(bits):
    if bits=="0":
        return 0,0.
    if not isinstance(bits,str) or not bits.startswith("1"):
        raise ValueError("bad model prefix")
    m,k = elias_gamma_decode(bits,1)
    q,end = elias_gamma_decode(bits,k)
    if end!=len(bits) or not (1 <= m <= 27) or not (2 <= q <= 451):
        raise ValueError("noncanonical model code")
    return m,(q-1)/1000

def nyquist36_receipt():
    """Exact integer 18 -> 36 orientation recovery, without claiming Shannon."""
    cos9 = tuple((1,0,-1,0)[j%4] for j in range(36))
    sin9 = tuple((0,1,0,-1)[j%4] for j in range(36))
    sin27 = tuple((0,-1,0,1)[j%4] for j in range(36))
    assert all(sin9[2*j]==sin27[2*j]==0 for j in range(18))
    assert sin9[1]==1 and sin27[1]==-1
    assert sum(x*y for x,y in zip(cos9,sin9))==0
    assert sum(x*x for x in sin9)==18
    assert sum(x*x for x in cos9)==18
    return {"coarse_sine_samples_zero":18,
            "fine_sine9_j1":sin9[1],"fine_sine27_j1":sin27[1],
            "cos_sin9_gram":0,"sin9_norm_squared":18,
            "not_a_continuous_sampling_theorem":True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pde",action="store_true")
    parser.add_argument("--optics",action="store_true")
    parser.add_argument("--rays",type=int,default=720)
    parser.add_argument("--segments",type=int,default=1536)
    parser.add_argument("--bounces",type=int,default=8)
    parser.add_argument("--controls",action="store_true",help="add non-369 m=4,5,7 controls")
    parser.add_argument("--torque-objective",choices=["min","max"],default="min")
    parser.add_argument("--output")
    args=parser.parse_args()
    output={"exact":exact_receipt(), "nyquist36":nyquist36_receipt(),
            "model_identity":"fresh_geometry_not_original_Kozyrev_experiment",
            "physical_torque_calibrated":False}
    if args.pde:
        output["pde"]={str(m):{"grid41":laplacian_eigenvalues(m,41),
                              "grid61":laplacian_eigenvalues(m,61)} for m in (3,6,9)}
    if args.optics:
        output["optics"]=optical_sweep(args.rays,args.segments,args.bounces,
                                       include_controls=args.controls)
        output["torque_objective"]=args.torque_objective
        output["pareto"]=pareto(output["optics"],args.torque_objective)
        output["alternate_pareto"]=pareto(output["optics"],
                                         "max" if args.torque_objective=="min" else "min")
        output["sample_ray"]=trace_ray(.37*math.pi,spiral_vertices(3,.12,args.segments),
                                       args.bounces,record=True)
    rendered=json.dumps(output,indent=2)
    if args.output:
        Path(args.output).write_text(rendered+"\n")
    print(rendered)

if __name__=="__main__":
    main()
