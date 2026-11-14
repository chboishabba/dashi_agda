#!/usr/bin/env python3
"""C2 SHA-pinned ENDF/B-VIII.1 original 14N(n,p)14C MF=3 MT=103.

Original NNDC ENDF/B-VIII.1, DOI 10.11578/endf/2571019:
neutrons-version.VIII.1/n-007_N_014.endf, MAT 725.
Original raw 1,253,924-byte source SHA-256 from independent
AvilaLabs/OpenBNCT evaluated-neutron-source-selection.json.
Do not extrapolate beyond evaluation or confuse raw MF3 with Doppler-
broadened or resonance-reconstructed cross sections.
"""
import argparse,bisect,csv,hashlib,json,math,re
from pathlib import Path

ORIGINAL_SHA="fd5c0c0beccefbcd0b57c49bcdf835449d2014e3740830377ce24760478c06d8"
ORIGINAL_BYTES=1253924
ORIGINAL_MAT=725
DOI="10.11578/endf/2571019"

def endf_float(x):
    v=x.strip()
    if not v:return 0.
    if "e" in v.lower():return float(v)
    m=re.fullmatch(r"([+-]?(?:\d+(?:\.\d*)?|\.\d+))([+-]\d+)",v)
    if m:return float(m.group(1)+"e"+m.group(2))
    return float(v)

def fields(line):
    if len(line)<75:raise ValueError("Short ENDF-6 line")
    return [line[k:k+11] for k in range(0,66,11)]

def section(path,mat=ORIGINAL_MAT,mf=3,mt=103):
    rows=[]
    for line in Path(path).read_text(encoding="ascii").splitlines():
        if len(line)<75:raise ValueError("Malformed ENDF source line")
        if (int(line[66:70]),int(line[70:72]),int(line[72:75]))==(mat,mf,mt):
            rows.append(line)
    if len(rows)<4:raise ValueError("Missing original MF3/MT103 N14 section")
    return rows

def get_grid(path,check_source_sha=True):
    path=Path(path); raw=path.read_bytes()
    sha=hashlib.sha256(raw).hexdigest()
    if check_source_sha and (sha!=ORIGINAL_SHA or len(raw)!=ORIGINAL_BYTES):
        raise ValueError("Wrong ENDF/B-VIII.1 N14 source hash or byte count: "+sha)
    lines=section(path)
    # Section first record HEAD; next record TAB1 QM,QI,LR,NR,NP.
    h=fields(lines[1]);nr=int(h[4]);np=int(h[5])
    if not 1<=nr<=1000 or not 2<=np<=500000:
        raise ValueError("Malformed TAB1 interpolation/point counts")
    # ENDF interpolation-list and XY-list each begin at NEW RECORD boundary;
    # padding on a final interpolation row is NOT an energy/XS point.
    n_interpolation_lines=(2*nr+5)//6
    n_data_lines=(2*np+5)//6
    if len(lines)<2+n_interpolation_lines+n_data_lines:
        raise ValueError("Truncated original MT103 table")
    interpolation_tokens=[v for row in lines[2:2+n_interpolation_lines]
                          for v in fields(row)]
    xy_tokens=[v for row in
               lines[2+n_interpolation_lines:2+n_interpolation_lines+n_data_lines]
               for v in fields(row)]
    regions=[]
    for i in range(nr):
        nbt=int(interpolation_tokens[2*i])
        law=int(interpolation_tokens[2*i+1])
        if law not in (1,2,3,4,5):raise ValueError("Unsupported ENDF interpolation")
        regions.append((nbt,law))
    if regions[-1][0]!=np or any(regions[j][0]<=regions[j-1][0]
                                for j in range(1,len(regions))):
        raise ValueError("Nonmonotone NBT region or NBT != NP")
    xy=[]
    for i in range(np):
        energy=endf_float(xy_tokens[2*i])
        barn=endf_float(xy_tokens[2*i+1])
        if not (math.isfinite(energy) and math.isfinite(barn)) or energy<=0 or barn<0:
            raise ValueError("Invalid original physical E/sigma")
        xy.append((energy,barn))
    if any(xy[i+1][0]<xy[i][0] for i in range(len(xy)-1)):
        raise ValueError("Unsorted evaluated energy grid")
    return {"original_sha256":sha,"mat":ORIGINAL_MAT,"mf":3,"mt":103,
            "nr":nr,"np":np,"interpolations":regions,"pairs":xy}

def interpolate(grid,energy):
    xy=grid["pairs"];energies=[p[0] for p in xy]
    if not xy[0][0]<=energy<=xy[-1][0]:
        raise ValueError("No extrapolation outside original evaluated range")
    i=bisect.bisect_right(energies,energy)
    if i>=len(xy):return xy[-1][1]
    if i==0:return xy[0][1]
    e0,y0=xy[i-1];e1,y1=xy[i]
    if energy==e0:return y0
    if e1==e0:raise ValueError("Duplicate energy with unresolved discontinuity")
    right_1_based_index=i+1
    law=next(scheme for bound,scheme in grid["interpolations"]
             if right_1_based_index<=bound)
    if law==1:return y0
    if law in (3,5):
        if e0<=0 or e1<=0:raise ValueError("Log energy invalid")
        frac=math.log(energy/e0)/math.log(e1/e0)
    else:frac=(energy-e0)/(e1-e0)
    if law in (4,5):
        if y0<=0 or y1<=0:raise ValueError("Log XS invalid")
        result=y0*math.exp(math.log(y1/y0)*frac)
    else:result=y0+(y1-y0)*frac
    if result<0 or not math.isfinite(result):
        raise ValueError("Nonphysical interpolated sigma")
    return result

def source_rate(grid,flux_rows,n14_atoms):
    """Convolve original evaluated XS with measured/modelled source spectrum.

    Integration is trapezoidal on union of cross-section and input-flux knots.
    No inferred body flux from outside-ground spectra.
    """
    if len(flux_rows)<2 or not math.isfinite(n14_atoms) or n14_atoms<0:
        raise ValueError("Invalid source spectrum or N14 population")
    energies=[row[0] for row in flux_rows]
    if any(not math.isfinite(e) or e<=0 for e in energies) or any(
            energies[i+1]<=energies[i] for i in range(len(energies)-1)):
        raise ValueError("Invalid flux energy grid")
    if any(not math.isfinite(f) or f<0 for _,f in flux_rows):
        raise ValueError("Invalid differential flux density")
    if energies[0]<grid["pairs"][0][0] or energies[-1]>grid["pairs"][-1][0]:
        raise ValueError("Full source flux not covered: evaluated support missing")
    knots=sorted(set(energies+[e for e,_ in grid["pairs"]
                               if energies[0]<e<energies[-1]]))
    def flux(e):
        i=bisect.bisect_right(energies,e)
        if i==0:return flux_rows[0][1]
        if i>=len(energies):return flux_rows[-1][1]
        e0,f0=flux_rows[i-1];e1,f1=flux_rows[i]
        return f0+(f1-f0)*(e-e0)/(e1-e0)
    integral=sum((e1-e0)/2*(flux(e0)*interpolate(grid,e0)
                           +flux(e1)*interpolate(grid,e1))
                 for e0,e1 in zip(knots[:-1],knots[1:]))
    return {
       "modelled_rate_per_second":integral*1e-24*n14_atoms,
       "spectrum_energy_eV":[energies[0],energies[-1]],
       "mesh_points":len(knots),
       "evaluation_covers_entire_input_spectrum":True,
       "body_attenuation_reconstructed":False,
       "not_a_measured_in_vivo_rate":True,
       "numerics":"piecewise trapezoid on joint energy knots; nonlinear-law integration approximate"
    }

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--endf",type=Path,required=True)
    ap.add_argument("--allow-unverified-source",action="store_true",
                    help="SYNTHETIC TEST ONLY; never physical-data acceptance")
    ap.add_argument("--flux-csv",type=Path)
    ap.add_argument("--target-n14-atoms",type=float)
    ap.add_argument("--out",type=Path)
    args=ap.parse_args()
    grid=get_grid(args.endf,not args.allow_unverified_source)
    result={
       "source_doi":DOI,
       "original_archive_path":"neutrons-version.VIII.1/n-007_N_014.endf",
       "original_file_sha256":grid["original_sha256"],
       "verified_original_bytes":not args.allow_unverified_source,
       "reaction":"14N(n,p)14C, ENDF MF3 MT103",
       "original_mat":grid["mat"],
       "interpolation_regions":grid["interpolations"],
       "evaluated_energy_range_eV":[grid["pairs"][0][0],grid["pairs"][-1][0]],
       "original_grid_points":grid["np"],
    }
    if args.flux_csv:
        if args.target_n14_atoms is None:ap.error("--flux-csv requires --target-n14-atoms")
        with args.flux_csv.open(newline="") as inp:
            r=csv.DictReader(inp)
            if set(r.fieldnames or [])!={"energy_eV","differential_flux_cm2_s_eV"}:
                raise ValueError("Incorrect source differential flux units")
            rows=[(float(x["energy_eV"]),float(x["differential_flux_cm2_s_eV"]))
                  for x in r]
        result["fold"]=source_rate(grid,rows,args.target_n14_atoms)
    txt=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.out:args.out.write_text(txt)
    print(txt)
if __name__=="__main__":main()
