#!/usr/bin/env python3
"""B2 MMS1-4 original-source tetrahedral Poynting finite-volume budget.

INPUT: 2+ synchronized, genuine source-CDF-SHA256-verified epochs; each has
MMS1..MMS4 GSE positions, E, B, *independently sourced* J (FPI moments or
source-qualified curlometer) and documented componentwise instrument error
bounds. Units: r km; E mV/m; B nT; J nA/m^2; times UTC.

A FIXED reference tetra is formed by shrinking the t0 spacecraft tetra
about its center. Every reference vertex MUST lie in each epoch's
spacecraft tetra, so the affine reconstructions only interpolate, never
extrapolate. Reconstructed E,B,J are affine *models*, not observations
between spacecraft. The face-integrated (E cross B)/mu0 and volume-
integrated J dot E are exactly integrated from those affine fields.
Space-time trapezoidal work/flux can leave unresolved temporal curvature.
The output reports a generous deterministic componentwise measurement
uncertainty bound, but DOES NOT bound affine model error, FPI current bias,
spacetime offsets, moving-tetra physics or missing displacement-current.

A four-probe tetrahedron is NOT an automatically accurate spatial boundary.
Only raw source-file verification (not receipts alone) permits the real
path. --self-test uses a plane-wave synthetic exact benchmark, labelled as
such. No raw original MMS files are bundled, guessed or fabricated.
"""
from __future__ import annotations
import argparse,hashlib,json,math
from datetime import datetime,timezone
from pathlib import Path

C=299792458.0
MU0=1.25663706212e-6
EPS0=1/(MU0*C*C)
REQUIRED=("mms1","mms2","mms3","mms4")
REQUIRED_SOURCE_INSTRUMENTS=("position","E","B","J")

def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def times(q,v):return tuple(q*x for x in v)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],
                       a[2]*b[0]-a[0]*b[2],
                       a[0]*b[1]-a[1]*b[0])
def norm(a):return math.sqrt(dot(a,a))
def det(a,b,c):return dot(a,cross(b,c))
def total(xs):return tuple(sum(a[i] for a in xs) for i in range(3))

def barycentric(vertices,pt):
    r0=vertices[0];a=sub(vertices[1],r0);b=sub(vertices[2],r0);c=sub(vertices[3],r0)
    den=det(a,b,c)
    edge=max(norm(sub(x,y)) for i,x in enumerate(vertices) for y in vertices[i+1:])
    if edge<=0 or abs(den)/6<1e-6*edge**3:
        raise ValueError("MMS tetrahedron degenerate or badly conditioned")
    d=sub(pt,r0)
    l1=det(d,b,c)/den;l2=det(a,d,c)/den;l3=det(a,b,d)/den
    return (1-l1-l2-l3,l1,l2,l3)

def interpolate(values,lambdas):
    return tuple(sum(lambdas[i]*values[i][j] for i in range(4)) for j in range(3))

def integral_bilinear_tetra(a,b,volume):
    """Exact for affine fields: integral_A.B = V/20*(sum A_i dot B_i + (sum A_i)dot(sum B_i))."""
    return volume*(sum(dot(x,y) for x,y in zip(a,b))+dot(total(a),total(b)))/20

def surface_flux(ref,E,B):
    flux=0.0;total_area=0.0
    for excluded in range(4):
        ids=[i for i in range(4) if i!=excluded]
        i,j,k=ids
        area=times(.5,cross(sub(ref[j],ref[i]),sub(ref[k],ref[i])))
        if dot(area,sub(ref[excluded],ref[i]))>0:
            area=times(-1,area)
        a=[E[n] for n in ids];b=[B[n] for n in ids]
        # Triangle barycentric moments: diagonal 1/6, off-diagonal 1/12.
        avg=times(1/12,plus(cross(total(a),total(b)),
                            total([cross(x,y) for x,y in zip(a,b)])))
        flux+=dot(area,avg)/MU0
        total_area+=norm(area)
    return flux,total_area

def spatial_integrals(ref,E,B,J):
    volume=abs(det(sub(ref[1],ref[0]),sub(ref[2],ref[0]),sub(ref[3],ref[0])))/6
    if volume<=0:raise ValueError("Zero reference volume")
    U=EPS0*.5*integral_bilinear_tetra(E,E,volume)
    U+=.5/MU0*integral_bilinear_tetra(B,B,volume)
    W=integral_bilinear_tetra(J,E,volume)
    F,A=surface_flux(ref,E,B)
    return {"volume_m3":volume,"surface_area_m2":A,
            "energy_J":U,"outward_flux_W":F,"current_work_W":W}

def parse_t(v):
    dt=datetime.fromisoformat(v.replace("Z","+00:00"))
    if dt.tzinfo is None:raise ValueError("MMS times must specify UTC")
    return dt.astimezone(timezone.utc).timestamp()

def sha256(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as file:
        for chunk in iter(lambda:file.read(1<<20),b""):h.update(chunk)
    return h.hexdigest()

def verify_sources(point,cache):
    for source in REQUIRED_SOURCE_INSTRUMENTS:
        obj=point.get("original_cdf",{}).get(source)
        if not isinstance(obj,dict):raise ValueError("Source CDF metadata missing: "+source)
        file=Path(obj.get("path",""))
        if not file.is_file():raise ValueError("Original file bytes missing: "+str(file))
        expected=obj.get("sha256","").lower()
        if len(expected)!=64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("Invalid raw CDF SHA256")
        if str(file) not in cache:cache[str(file)]=sha256(file)
        if cache[str(file)]!=expected:
            raise ValueError("Raw CDF SHA mismatch: "+str(file))
        # This verifies file identity, not the actual variable's source/probe.
        # Source variable/probe/time/quality trace still needs independent
        # source-attribute and detector provenance at the acquisition stage.
    if point.get("quality_E")!="pass" or point.get("quality_B")!="pass" or point.get("quality_J")!="pass":
        raise ValueError("Original instrument quality flag not passed")

def epoch(raw,cache,synthetic=False,max_skew_s=.02):
    t=parse_t(raw["time_utc"])
    points=raw["spacecraft"]
    if len(points)!=4 or set(p["id"].lower() for p in points)!=set(REQUIRED):
        raise ValueError("All four distinct MMS spacecraft required")
    points=sorted(points,key=lambda z:z["id"].lower())
    result={"t":t,"r":[],"E":[],"B":[],"J":[]}
    errors=[]
    for p in points:
        if abs(parse_t(p["sample_time_utc"])-t)>max_skew_s:
            raise ValueError("MMS measurement epoch too far from common time")
        if not synthetic:verify_sources(p,cache)
        for key,scale,field in (("position_GSE_km",1000.,"r"),
                                ("E_GSE_mV_m",1e-3,"E"),
                                ("B_GSE_nT",1e-9,"B"),
                                ("J_GSE_nA_m2",1e-9,"J")):
            v=p.get(key)
            if not isinstance(v,list) or len(v)!=3 or any(
                not isinstance(x,(int,float)) or not math.isfinite(x) for x in v):
                raise ValueError("Missing calibrated GSE 3-vector: "+key)
            result[field].append(tuple(float(x)*scale for x in v))
        vals=[]
        for key,scale in (("E_component_abs_error_mV_m",1e-3),
                          ("B_component_abs_error_nT",1e-9),
                          ("J_component_abs_error_nA_m2",1e-9)):
            v=p.get(key)
            if not isinstance(v,(int,float)) or not math.isfinite(v) or v<0 or (v==0 and not synthetic):
                raise ValueError("No source-qualified positive component error: "+key)
            vals.append(v*scale)
        errors.append(vals)
    result["uncertainty"]=tuple(math.sqrt(3)*max(r[i] for r in errors) for i in range(3))
    return result

def refine_reference(a,b,scale):
    if not 0<scale<1:raise ValueError("Reference shrink requires 0<scale<1")
    ca=times(.25,total(a["r"]))
    ref=[plus(ca,times(scale,sub(v,ca))) for v in a["r"]]
    # Both spatial interpolations must be convex, never extrapolated.
    for src in (a,b):
        for pt in ref:
            weights=barycentric(src["r"],pt)
            if min(weights)<-1e-8 or max(weights)>1+1e-8:
                raise ValueError("Fixed reference tetra leaves actual MMS source hull")
    return ref

def interpolate_epoch(ep,ref):
    fields={}
    for typ in ("E","B","J"):
        fields[typ]=[interpolate(ep[typ],barycentric(ep["r"],p)) for p in ref]
    fields.update(spatial_integrals(ref,fields["E"],fields["B"],fields["J"]))
    Emax=max(map(norm,fields["E"]));Bmax=max(map(norm,fields["B"]));Jmax=max(map(norm,fields["J"]))
    de,db,dj=ep["uncertainty"];V=fields["volume_m3"];A=fields["surface_area_m2"]
    fields["error_energy_J"]=V*(EPS0/2*(2*Emax*de+de*de)+
                               1/(2*MU0)*(2*Bmax*db+db*db))
    fields["error_flux_W"]=A/MU0*(Emax*db+Bmax*de+de*db)
    fields["error_work_W"]=V*(Jmax*de+Emax*dj+dj*de)
    return fields

def analyze(payload,synthetic=False,scale=.5,max_skew_s=.02):
    if payload.get("schema")!="dashi.ksw668.mms4-tetra-original-v1":
        raise ValueError("Wrong exact four-spacecraft original source schema")
    if payload.get("reference_frame")!="GSE":
        raise ValueError("MMS source must be in calibrated GSE")
    if payload.get("spatial_model")!="affine_4_spacecraft_interpolation":
        raise ValueError("Missing explicit affine spatial modelling assumption")
    epochs=payload.get("epochs",[])
    if len(epochs)!=2:raise ValueError("Exactly two snapshots required for this order-2 time estimate")
    cache={}
    states=[epoch(x,cache,synthetic,max_skew_s) for x in epochs]
    a,b=states
    dt=b["t"]-a["t"]
    if not .00000001<dt<=30:raise ValueError("Invalid MMS temporal baseline")
    ref=refine_reference(a,b,scale)
    u0=interpolate_epoch(a,ref);u1=interpolate_epoch(b,ref)
    integrated_flux=.5*dt*(u0["outward_flux_W"]+u1["outward_flux_W"])
    integrated_work=.5*dt*(u0["current_work_W"]+u1["current_work_W"])
    change=u1["energy_J"]-u0["energy_J"]
    residual=change+integrated_flux+integrated_work
    error=(u0["error_energy_J"]+u1["error_energy_J"]+
           .5*dt*sum(u["error_flux_W"]+u["error_work_W"] for u in (u0,u1)))
    return {
      "schema":"dashi.ksw668.mms4-affine-tetra-poynting.v1",
      "status":"SYNTHETIC MATHEMATICAL TEST ONLY" if synthetic else
               "RAW CDF SHA-VERIFIED, PHYSICAL INTERPOLATION MODEL STILL UNCERTAIN",
      "fixed_ref_spatial_model":"affine GSE four-spacecraft convex interpolation",
      "source_raw_CDF_files_verified":0 if synthetic else len(cache),
      "same_region_both_epochs_convex_hull_only":True,
      "source_temporal_skew_upper_seconds":max_skew_s,
      "time_difference_seconds":dt,"reference_tetra_volume_m3":u0["volume_m3"],
      "instantaneous":[{k:u[k] for k in ("energy_J","outward_flux_W","current_work_W")}
                         for u in (u0,u1)],
      "delta_volume_field_energy_J":change,
      "integrated_outward_poynting_J":integrated_flux,
      "integrated_JdotE_J":integrated_work,
      "unclosed_budget_residual_J":residual,
      "component_uncertainty_only_residual_upper_J":error,
      "temporal_trapezoid_error_qualified":False,
      "affine_model_interpolation_error_qualified":False,
      "same_source_original_instrument_CDF_provenance_attested":not synthetic,
      "same_original_MMS_20170617_CDF_measurement":not synthetic,
      "source_physical_boundary_empirically_accepted":False,
    }

def synthetic_plane_wave():
    # E_y=f(x-ct), B_z=E/c, J=0 solves Maxwell exactly. Interior affine
    # reconstruction and *both* finite-volume source integrations are exact.
    # Reference tetra is fixed, not a moving spacecraft face.
    t0=1700000000.
    times=[t0,t0+.001]
    base=((0,0,0),(100,0,0),(0,100,0),(0,0,100))
    rows=[]
    for i,t in enumerate(times):
        points=[]
        for j,r in enumerate(base):
            f=.02+1e-9*(r[0]-C*(t-t0))
            points.append({
              "id":REQUIRED[j],
              "sample_time_utc":datetime.fromtimestamp(t,timezone.utc).isoformat(),
              "position_GSE_km":[x/1000 for x in r],
              "E_GSE_mV_m":[0,f*1000,0],
              "B_GSE_nT":[0,0,f/C*1e9],
              "J_GSE_nA_m2":[0,0,0],
              "E_component_abs_error_mV_m":0.,
              "B_component_abs_error_nT":0.,
              "J_component_abs_error_nA_m2":0.,
            })
        rows.append({"time_utc":datetime.fromtimestamp(t,timezone.utc).isoformat(),
                     "spacecraft":points})
    payload={"schema":"dashi.ksw668.mms4-tetra-original-v1",
             "reference_frame":"GSE",
             "spatial_model":"affine_4_spacecraft_interpolation",
             "epochs":rows}
    result=analyze(payload,True)
    scale=max(1e-30,abs(result["delta_volume_field_energy_J"]))
    # Time-trapezoid exact for f=a+b(x-ct): flux and dU/dt linear in t.
    assert abs(result["unclosed_budget_residual_J"])<2e-7*scale
    assert abs(result["integrated_outward_poynting_J"])>0
    assert result["reference_tetra_volume_m3"]>0
    result["synthetic_maxwell_plane_wave_residual_verified"]=True
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input",type=Path)
    p.add_argument("--self-test",action="store_true")
    p.add_argument("--reference-shrink",type=float,default=.5)
    p.add_argument("--max-skew-s",type=float,default=.02)
    p.add_argument("--out",type=Path)
    ns=p.parse_args()
    if ns.self_test:
        if ns.input:p.error("--input and --self-test cannot be combined")
        r=synthetic_plane_wave()
    else:
        if not ns.input:p.error("--input required for original data")
        r=analyze(json.loads(ns.input.read_text()),False,ns.reference_shrink,ns.max_skew_s)
    report=json.dumps(r,indent=2,sort_keys=True)+"\n"
    if ns.out:ns.out.write_text(report)
    print(report)

if __name__=="__main__":
    main()
