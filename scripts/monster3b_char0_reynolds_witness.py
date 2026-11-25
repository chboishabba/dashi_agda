#!/usr/bin/env python3
"""Construct a compact exact characteristic-zero intertwiner expression.

Conway's rational Monster lattice reduces to MMV(p), per mmgroup API.
For the genuine normalizer cover H=6.Suz:2, 31 is a unit in |H|.
Lift a certified modular source->actual Hom map to the original Conway
lattice, project to the actual marked vacuum, then Reynolds-average.
The resulting group-algebra expression is an exact characteristic-zero
witness (conditional on the authenticated integral-source hypotheses).
It is NOT an evaluation of the enormous group sum into dense matrices.
"""
import argparse, hashlib, json
from pathlib import Path
import numpy as np
from monster3b_actual_projective_sym2_intertwiner import inverse
from monster3b_single_residual_frame import source_frame
from monster3b_lindsey_actual_mod31_join import source_matrices, dual

P=31
H_ORDER=5380145971200
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def require(b,msg):
    if not b:raise ValueError(msg)
def run(a):
    require(H_ORDER%P!=0,"bad prime for source cover")
    cover,phase,outer,canonical,join,manifest=map(read,(
        a.cover,a.phase,a.outer/"actual_MM31_outer_phase_result.json",
        a.canonical/"canonical_signed_normalizer_report.json",
        a.join/"lindsey_actual_MM31_report.json",a.manifest))
    packet=a.canonical/"canonical_signed_normalizer_mod31.npz"
    transport=a.join/"lindsey_to_actual_MM31_signed_intertwiners.npz"
    require(phase.get("status")=="LITERAL_MM_STANDARD_D_PHASE_RECOVERED"
            and phase.get("cover_sha256")==sha(a.cover)
            and phase.get("manifest_sha256")==sha(a.manifest),"literal phase receipt not attached")
    require(phase.get("raw_wheel_has_order13") is True and phase.get("literal_wheel_13_defect_z_power")==0,
            "literal cyclic source word has a retained central order defect or is unexecuted")
    require(join.get("status")=="ORIGINAL_ORDINARY_SOURCE_TO_ACTUAL_MM31_SIGNED_OPERATOR_WELD"
            and join.get("cover_sha256")==sha(a.cover)
            and join.get("model_sha256")==sha(a.model)
            and join.get("source_sha256")==sha(a.source)
            and join.get("packet_sha256")==sha(packet)
            and join.get("transport_sha256")==sha(transport)
            and join.get("D_relative_to_standard_phase")==phase.get("Q7_central_z_power"),
            "actual signed join/phase mismatch")
    require(canonical.get("status")=="SOURCE_BOUND_MOD31_SIGNED_GENERATOR_WELD"
            and canonical.get("operator_packet_sha256")==sha(packet)
            and canonical.get("model_sha256")==sha(a.model)
            and canonical.get("outer_receipt_sha256")==sha(a.outer/"actual_MM31_outer_phase_result.json"),
            "canonical packet provenance mismatch")
    require(outer.get("manifest_sha256")==sha(a.manifest)
            and outer.get("cover_sha256")==sha(a.cover),"original phase reconstruction provenance")
    for k in ("canonical_C_word","canonical_D_word"):
        require(outer.get(k)==cover.get(k)==phase.get(k) and bool(cover.get(k)),"source word mismatch")
    # A verified modular transport points actual -> ordinary. Invert
    # to form the seed ordinary -> actual in the exact original vacuum.
    with np.load(transport,allow_pickle=False) as f:
        maps={n:np.asarray(f["transport"+str(n)],dtype=np.int64)%P for n in (12,78)}
    for n,F in maps.items():
        require(F.shape==(2*n,2*n),"signed transport shape")
        require(not np.any(F[:n,n:]) and not np.any(F[n:,:n]),"phase mixing")
    seeds={}
    for j,(label,folder,z) in enumerate((("plus",a.plus,5),("minus",a.minus,25))):
        amb=folder/"ambient_basis_rows_mod31.npz"
        if not amb.is_file():amb=folder/"ambient_basis_rows.npz"
        eig=folder/"actual_C2_12_78_mod31.npz"
        st=folder/"mmv31_hom_status.json"
        for path in (amb,eig,st):
            require(outer["source_packet_sha256"].get(label+"/"+path.name)==sha(path),
                    "changed original phase source "+str(path))
        state=read(st)
        require((state.get("p"),state.get("zeta_mod_p"),
                state.get("number_independent_B_fixed_vectors"))==(31,z,90),"wrong marked vacuum")
        with np.load(amb,allow_pickle=False) as f:
            rows=f["rows"];piv=np.asarray(f["pivots"],dtype=np.int64)
            require(rows.shape==(90,196884) and piv.shape==(90,),"ambient source dimensions")
            minor=np.asarray(rows[:,piv],dtype=np.int64)%P
            inverse(minor)
        seed={"phase":j+1,"root_mod31":z,"ambient_file":str(amb.resolve()),
              "ambient_sha256":sha(amb),"eigenbasis_sha256":sha(eig),
              "basis_coordinates":{}}
        with np.load(eig,allow_pickle=False) as f:
            for n,F in maps.items():
                B=np.asarray(f["eig"+str(n)],dtype=np.int64)%P
                require(B.shape==(90,n),"source eigenspace shape")
                X=B@inverse(F[j*n:(j+1)*n,j*n:(j+1)*n])%P
                seed["basis_coordinates"][str(n)]=X.tolist()
        seeds[label]=seed
    T=source_matrices(read(a.source),phase["Q7_central_z_power"])
    U={g:dual(T[g],g=="C") for g in T}
    compact={}
    for n,src in ((12,T),(78,U)):
        r=source_frame({g:src[g][:n,:n] for g in ("D","E")})
        recorded=canonical.get("source_C13_orbits",{}).get(str(n),{})
        if recorded:
            require(r["words"]==recorded["words"],"cyclic source basis receipt mismatch")
        compact[str(n)]={"word_basis":r["words"],"selected_residual_index":r["index"],
            "source_seed":"e0","exact_recipe":r["exact_recipe"],
            "mod31_certificate":r,
            "exact_projector":"P_L=p(R_L)/p(0), with p=det(tI-R_A)/t over Q(zeta); do not lift modular polynomial coefficients",
            "exact_dual_recovery":"U_i=P_L sum_j (H^-1)_ij L(w_j)^-1; H is computed on the exact source, not lifted mod31",
            "positive_seed":"P_L P_sector P_s P_B lift(ambient_rows)^T lift(basis_coordinates[:,0])",
            "positive_F":"columns L(w_i)y times B^-1",
            "negative_F":"L(C)_(plus->minus) F_plus A(C)_(plus->minus)^-1",
            "vacuum_sector":"(I-L(C^2))/2" if n==12 else "(I+L(C^2))/2"}
    return {"status":"EXACT_CHAR0_CYCLIC_EXPRESSION_FROM_ACTUAL_MOD31",
        "numeric_characteristic_zero_matrices_evaluated":False,
        "conditional_on_authenticated_Conway_lattice_and_full_cover":True,
        "field":"Q(zeta), zeta^2+zeta+1=0",
        "local_prime":"(31,zeta-5)","group_order":H_ORDER,
        "right_action_coefficient_columns":True,
        "source":str(a.source.resolve()),"source_sha256":sha(a.source),
        "manifest_sha256":sha(a.manifest),"cover_sha256":sha(a.cover),
        "model_sha256":sha(a.model),"transport_sha256":sha(transport),
        "actual_C":phase["canonical_C_word"],"actual_D":phase["canonical_D_word"],
        "actual_standard_D":phase["standard_D_word"],"actual_Q7":phase["Q7_word"],
        "actual_D_phase":phase["Q7_central_z_power"],
        "actual_order13_word":phase["literal_wheel_word"],
        "actual_order13_defect_word":phase["literal_wheel_13_defect_word"],
        "center_word":manifest["center_word"],
        "modulation_words":manifest["modulation_words"],
        "translation_words":manifest["translation_words"],
        "seeds":seeds,
        "seed_expression":"X_s = P_zeta^s P_B (lift(ambient_rows_s)^T lift(basis_coordinates_s))",
        "target_operator":"L(g) from original Conway rho(g) by the exact tensor evaluation and canonical 729 Weil inverse; preserve signed phase",
        "compact_seed_projectors":compact,
        "intertwiner_expression":"Use compact_seed_projectors: apply the sector and single-residual exact polynomial projector to the lifted positive seed, reconstruct all source orbit columns and derive the negative phase by C; no group enumeration.",
        "reynolds_existence_expression":"F = (1/|H|) sum_(g in H) L(g) X A(g)^(-1), separately for signed 24 and 156",
        "compact_proof":"The actual modular isomorphism and integral hypotheses imply the characteristic-zero isomorphism by Reynolds. The source cyclic basis is invertible at the marked prime. The selected R_A kills e0; R_A and R_A^2 have rank n-1 modulo 31, hence also in char0, and p(0) is a local unit. Thus p(R_L)/p(0) projects onto the transported seed line. The source dual orbit pairing is invertible at 31 and in characteristic zero; its exact inverse supplies recovery without a Hermitian Gram calculation. Sector projection and the polynomial preserve the certified modular seed; cyclic reconstruction and outer transport preserve the full certified modular intertwiner. No dense characteristic-zero evaluations are claimed.",
        "proof":"Reduction of X is the checked inverse modular transport. Every summand reduces to X since X intertwines on the generators and therefore H. |H| is a unit. F reduces to the invertible modular transport, so F is an actual characteristic-zero isomorphism; no entrywise rational lift of MMV operators is asserted."}
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source",type=Path,default=Path(__file__).resolve().parents[1]/"Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json")
    for name in ("manifest","cover","phase","model","outer","canonical","join","plus","minus","out"):
        p.add_argument("--"+name,type=Path,required=True)
    a=p.parse_args();a.out.parent.mkdir(parents=True,exist_ok=True)
    try:r=run(a)
    except Exception as exc:r={"status":"BLOCKED_OR_SOURCE_RESIDUAL","error":repr(exc)}
    a.out.write_text(json.dumps(r,indent=2)+"\n");print(r["status"])
    return 0 if r["status"].startswith("EXACT_CHAR0") else 2
if __name__=="__main__":raise SystemExit(main())
