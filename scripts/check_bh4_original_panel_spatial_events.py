#!/usr/bin/env python3
"""Original acquired 29×12 Rhea reaction panel on one shared 3×3×3 spatial state.

Consumes the EXISTING source certificate and EXISTING deterministic builder:
  acquire_rhea_chebi_bh4_reactions.py
    -> build_bh4_stoichiometric_matrix.py
    -> run_bh4_reaction_network.py

No hand-made 12 reaction list, 29 synthetic species, fake zero columns,
irreversible BH4-cofactor consumption, or inferred 29 exchange fluxes.

For each source-acquired *finite* original reaction column:
  1. verify original atom/charge balance and participant identity;
  2. apply exact nonnegative integer molecular events in a selected voxel;
  3. prove by recomputation that the shared spatial molecule inventory
     has conserved CHNOP atoms and integer electric charge.
For transport: test every one of the 54 original 3D bonds in both
directions for every source-acquired finite species.

Source identity/stoichiometry is distinct from measured rates, local
compartment assignment, external exchange or clinical causal mechanism.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from itertools import product
from pathlib import Path

from build_bh4_stoichiometric_matrix import build_matrix, participant_key
from run_bh4_reaction_network import QDPR, audit_reaction, parse_formula
from run_bh4_flux_feasibility import evaluate as evaluate_original_flux_candidate

ROOT=Path(__file__).resolve().parents[1]
CANONICAL_OWNER=ROOT/"DASHI/Biology/Molecular/BH4ExecutedPanelReactionReceiptExact.agda"
POINTS=tuple(product((-1,0,1),repeat=3))
BONDS=tuple((p,tuple(p[i]+int(i==axis) for i in range(3)))
       for p in POINTS for axis in range(3) if p[axis]<1)
assert len(POINTS)==27 and len(BONDS)==54
ELEMENTS=("C","H","N","O","P")


def reject_duplicate_json_keys(pairs):
    """Keep original source and candidate coordinates unambiguous."""
    result={}
    for key,value in pairs:
        if key in result:
            raise ValueError(f"duplicate key in source JSON: {key!r}")
        result[key]=value
    return result


def reject_nonfinite_json_constant(value):
    raise ValueError(f"nonfinite source JSON numeric literal: {value}")


def load_original_receipt_json(data):
    """Reject duplicate source keys and non-standard NaN/Infinity literals."""
    return json.loads(data,object_pairs_hook=reject_duplicate_json_keys,
                      parse_constant=reject_nonfinite_json_constant)


def check_certificate(certificate, *, full_panel):
    if not isinstance(certificate,dict) or not isinstance(certificate.get("reactions"),list):
        raise ValueError("acquired Rhea certificate reactions required")
    if full_panel and certificate.get("schema") != "dashi.rhea-chebi-bh4-panel.v2":
        raise ValueError("wrong actual original Rhea certificate schema")
    constructed=build_matrix(certificate)
    species=constructed["species_index"]
    reactions=constructed["reaction_index"]
    matrix=constructed["matrix"]
    residuals=constructed["finite_formula_residuals"]
    assert len(matrix)==len(species)
    assert all(len(row)==len(reactions) for row in matrix)
    if full_panel:
        if len(species)!=29 or len(reactions)!=12 or len(residuals)!=3:
            raise ValueError("original 29×12/3-residual acquisition not present")
        original_source=CANONICAL_OWNER.read_text(encoding="utf-8")
        for rid in reactions:
            if f'"{rid}"' not in original_source:
                raise ValueError(f"reaction not in source-written original panel: {rid}")
        for row in residuals:
            if f'"{row["rhea_id"]}"' not in original_source:
                raise ValueError("original nonfinite residual not retained")
    if len(set(species))!=len(species) or len(set(reactions))!=len(reactions):
        raise ValueError("duplicate source species/reaction")
    if constructed.get("external_exchange") != []:
        raise ValueError("internal S may not silently absorb external exchanges")
    by_species={}
    by_reaction={}
    for record in certificate["reactions"]:
        if not record.get("formula_charge_ready"):
            continue
        rid=str(record.get("rhea_id",""))
        if rid in by_reaction:
            raise ValueError("duplicated finite Rhea reaction")
        by_reaction[rid]=record
        audited=audit_reaction({"rhea_id":rid,"participants":record["participants"]})
        if not audited["stoichiometrically_balanced"]:
            raise ValueError(f"original reaction atom/charge not balanced: {rid}")
        for participant in record["participants"]:
            key=participant_key(participant)
            data=(parse_formula(str(participant["formula"])),
                  int(participant["charge"]))
            if key in by_species and by_species[key]!=data:
                raise ValueError(f"inconsistent original species formula/charge: {key}")
            by_species[key]=data
    if set(by_reaction)!=set(reactions) or set(by_species)!=set(species):
        raise ValueError("source participants do not match matrix species/reactions")
    for col in range(len(reactions)):
        for element in ELEMENTS:
            net=sum(int(matrix[i][col])*by_species[species[i]][0][element]
                    for i in range(len(species)))
            if net!=0:
                raise ValueError(f"source panel reaction {reactions[col]} changes {element}: {net}")
        charge=sum(int(matrix[i][col])*by_species[species[i]][1]
                   for i in range(len(species)))
        if charge!=0:
            raise ValueError(f"source panel reaction {reactions[col]} changes electric charge")
        if not any(matrix[i][col] for i in range(len(species))):
            raise ValueError("zero-column reaction may not represent acquired physical chemistry")
    return constructed,by_species


def inventory(species):
    return {(p,key):0 for p in POINTS for key in species}


def totals(state,by_species):
    elements=tuple(sum(count*by_species[key][0][element]
                       for (point,key),count in state.items())
                   for element in ELEMENTS)
    charge=sum(count*by_species[key][1] for (point,key),count in state.items())
    return elements,charge


def reaction_event(state,matrix,species,index,point,count,by_species):
    if point not in POINTS or type(count) is not int or count<0:
        raise ValueError("invalid physical voxel or reaction-event count")
    current=state.copy()
    column=[int(row[index]) for row in matrix]
    for key,coefficient in zip(species,column):
        if coefficient<0 and current[point,key]<-count*coefficient:
            raise ValueError("missing source-selected original reactants")
    old=totals(state,by_species)
    for key,coefficient in zip(species,column):
        current[point,key]+=count*coefficient
        if current[point,key]<0:
            raise AssertionError("negative molecular inventory")
    if totals(current,by_species)!=old:
        raise AssertionError("molecular atom or charge balance violated")
    return current


def transport_event(state,species,origin,target,key,by_species):
    if ((origin,target) not in BONDS and (target,origin) not in BONDS):
        raise ValueError("fictitious original cube bond")
    current=state.copy()
    if current[origin,key]:
        current[origin,key]-=1
        current[target,key]+=1
    if totals(current,by_species)!=totals(state,by_species):
        raise AssertionError("intervoxel material transfer changed atoms/charge")
    return current



# Explicit original cubical exterior interfaces; the face is NOT an
# assumed cellular membrane or measured vascular route.
OUTER_FACES={(axis,side): frozenset(
    point for point in POINTS if point[axis]==side)
    for axis in range(3) for side in (-1,1)}


def boundary_species_event(state,metadata,*,face,point,key,direction,
                           amount,source_reference):
    """Apply one provenance-labelled external event, returning its ledger.

    The return ledger is in CHNOP atoms and signed electric charge.
    A requested extraction removes only *available* molecules; missing
    original physiological flux is never represented by a fake zero.
    """
    if (face not in OUTER_FACES or point not in OUTER_FACES[face]
            or key not in metadata or direction not in ("inject","extract")
            or type(amount) is not int or amount<0
            or not isinstance(source_reference,str)
            or not source_reference.strip()):
        raise ValueError("unpaid or non-geometric original exterior exchange")
    actual=(amount if direction=="inject"
            else min(amount,state[point,key]))
    direction_sign=1 if direction=="inject" else -1
    after=state.copy()
    after[point,key]+=direction_sign*actual
    if after[point,key]<0:
        raise AssertionError("external exchange produced negative inventory")
    for other in POINTS:
        for species_key in metadata:
            if (other,species_key)!=(point,key):
                if after[other,species_key]!=state[other,species_key]:
                    raise AssertionError("external event changed unrelated voxel/species")
    formula,charge=metadata[key]
    external=(tuple(direction_sign*actual*formula[element]
                    for element in ELEMENTS),
              direction_sign*actual*charge)
    old_elements,old_charge=totals(state,metadata)
    new_elements,new_charge=totals(after,metadata)
    if (tuple(new_elements[i]-old_elements[i]
              for i in range(len(ELEMENTS))),
        new_charge-old_charge)!=external:
        raise AssertionError("source-paid external CHNOP/charge ledger inconsistent")
    return after,external,actual


def site_conserved_quantities(state,metadata,point):
    """Exact local C/H/N/O/P and signed integer charge at one 3D voxel."""
    atoms=tuple(sum(state[point,key]*metadata[key][0][element]
                    for key in metadata) for element in ELEMENTS)
    charge=sum(state[point,key]*metadata[key][1] for key in metadata)
    return atoms+(charge,)


def assert_original_voxel_continuity(initial,state,metadata,divergence,source,
                                    *,event_kind="audited"):
    """Check the exact six-coordinate balance on ALL original 27 sites."""
    for point in POINTS:
        after=site_conserved_quantities(state,metadata,point)
        before=site_conserved_quantities(initial,metadata,point)
        for i in range(6):
            if after[i]-before[i]+divergence[point][i]!=source[point][i]:
                raise AssertionError(
                    f"local original CHNOP/charge continuity failed: "
                    f"voxel={point}, coordinate={i}, event={event_kind}"
                )


def run_original_spatial_event_history(initial,matrix,species,metadata,events):
    """Chronological *local* conservation of real Rhea chemistry and flux.

    Accumulates transport divergence and boundary sources for EACH of the
    original 27 voxels, not just global totals. Reaction increments must
    annihilate each local CHNOP/charge quantity. Native current follows
    actual (not requested) one-quantum movement; face output is capped by
    available material. All inputs remain synthetic until source-paid.
    """
    if set(metadata)!=set(species) or set(initial)!={(p,key) for p in POINTS for key in species}:
        raise ValueError("physical history must use exact original species and 3D state")
    if any(type(v) is not int or v<0 for v in initial.values()):
        raise ValueError("invalid original nonnegative molecular inventory")
    state=initial.copy()
    source={point:[0]*6 for point in POINTS}
    divergence={point:[0]*6 for point in POINTS}
    event_checks=0
    for event in events:
        if not isinstance(event,dict):
            raise ValueError("original spatial event must be a typed record")
        event_kind=event.get("kind")
        if event_kind=="reaction":
            col=event["column"]
            point=event["point"]
            count=event["count"]
            if type(col) is not int or not 0<=col<len(matrix[0]):
                raise ValueError("reaction column not in original acquired finite matrix")
            state=reaction_event(state,matrix,species,col,point,count,metadata)
        elif event_kind=="native_transport":
            point=event["source"]
            target=event["target"]
            key=event["species"]
            if key not in metadata:
                raise ValueError("nonoriginal transport species")
            if (point,target) not in BONDS and (target,point) not in BONDS:
                raise ValueError("not an original 54-bond native transfer")
            moved=int(state[point,key]>0)
            state=transport_event(state,species,point,target,key,metadata)
            atom_counts,charge=metadata[key]
            flux=[moved*atom_counts[element] for element in ELEMENTS]+[moved*charge]
            for i,value in enumerate(flux):
                divergence[point][i]+=value
                divergence[target][i]-=value
        elif event_kind=="outer_face_exchange":
            point=event["point"]
            state,external,_=boundary_species_event(
                state,metadata,face=event["face"],point=point,
                key=event["species"],direction=event["direction"],
                amount=event["amount"],
                source_reference=event["source_reference"])
            for i,value in enumerate(external[0]+(external[1],)):
                source[point][i]+=value
        else:
            raise ValueError("unrecognized original chemistry/transport event")
        # The exact finite-volume law must hold at EACH voxel, including
        # voxels untouched by a reaction, transfer or environmental event.
        assert_original_voxel_continuity(
            initial,state,metadata,divergence,source,event_kind=event_kind)
        event_checks+=len(POINTS)
        if any(v<0 for v in state.values()):
            raise AssertionError("negative inventory in chronological history")
    ext_atoms=tuple(sum(source[point][i] for point in POINTS)
                    for i in range(len(ELEMENTS)))
    ext_charge=sum(source[point][-1] for point in POINTS)
    original=totals(initial,metadata)
    final=totals(state,metadata)
    if (tuple(final[0][i]-original[0][i] for i in range(len(ELEMENTS))),
        final[1]-original[1])!=(ext_atoms,ext_charge):
        raise AssertionError("all-history environmental balance failed")
    if any(sum(divergence[point][i] for point in POINTS)!=0 for i in range(6)):
        raise AssertionError("native cubical bond currents fail global cancellation")
    return state,{"external_CHNOP":ext_atoms,
                  "external_signed_charge":ext_charge,
                  "history_length":len(events),
                  "local_voxel_event_checks":event_checks,
                  "native_divergence_zero_global":True,
                  "local_CHNOP_and_signed_charge":True}


def test_source(certificate,*,full_panel):
    original,metadata=check_certificate(certificate,full_panel=full_panel)
    matrix=original["matrix"];species=original["species_index"]
    start=POINTS[0]
    # All 27 ORIGINAL cubical positions must support the SAME
    # source-certified finite reaction, without changing any other voxel.
    # Verify every molecular coordinate, not only a global sum: a
    # compensating remote mutation could conserve totals but still be
    # physically unrelated to the selected localized reaction.
    event_cases=0
    local_coordinate_checks=0
    for col in range(len(original["reaction_index"])):
        for point in POINTS:
            before=inventory(species)
            for i,key in enumerate(species):
                if matrix[i][col]<0:
                    before[point,key]=-int(matrix[i][col])
            after=reaction_event(before,matrix,species,col,point,1,metadata)
            assert totals(before,metadata)==totals(after,metadata)
            for other in POINTS:
                for i,key in enumerate(species):
                    expected=before[other,key]
                    if other==point:
                        expected+=int(matrix[i][col])
                    if after[other,key]!=expected:
                        raise AssertionError(
                            "original spatial reaction changes nonlocal/incorrect species "
                            f"at {other}: reaction={original['reaction_index'][col]} species={key}"
                        )
                    local_coordinate_checks+=1
            event_cases+=1
    # A genuinely shared chronological chemical/transport history for
    # EACH original finite reaction: react at a source voxel, transport one
    # generated product over a real neighbour, and return it. This checks
    # that the two operators consume the SAME inventory, rather than merely
    # testing unrelated single-event fixtures.
    source,target=BONDS[0]
    mixed_history_cases=0
    for col in range(len(original["reaction_index"])):
        initial=inventory(species)
        for i,key in enumerate(species):
            if matrix[i][col]<0:
                initial[source,key]=-int(matrix[i][col])
        reacted=reaction_event(initial,matrix,species,col,source,1,metadata)
        products=[species[i] for i in range(len(species))
                  if matrix[i][col]>0]
        if not products:
            raise ValueError("original reaction lacks movable product")
        key=products[0]
        outward=transport_event(reacted,species,source,target,key,metadata)
        returned=transport_event(outward,species,target,source,key,metadata)
        if returned != reacted:
            raise AssertionError("roundtrip on original native bond changed physical inventory")
        if not (totals(initial,metadata)==totals(outward,metadata)==totals(returned,metadata)):
            raise AssertionError("combined original reaction/transport breaks atom or charge balance")
        if any(v<0 for v in outward.values()):
            raise AssertionError("negative inventory in same-state spatial history")
        mixed_history_cases+=1
    # One actual mixed chemistry/native-transport/exterior-face history.
    # Provenance label is explicitly SYNTHETIC unless independently paid.
    # The demonstration never claims a real physiological exchange rate.
    mixed_boundary_cases=0
    for col in range(len(original["reaction_index"])):
        source,target=BONDS[0]
        initial=inventory(species)
        for i,key in enumerate(species):
            if matrix[i][col]<0:
                initial[source,key]=-int(matrix[i][col])
        product=next((species[i] for i in range(len(species))
                      if matrix[i][col]>0),None)
        if product is None:
            raise ValueError("original finite reaction has no product")
        face=(0,-1)
        if source not in OUTER_FACES[face]:
            raise AssertionError("selected native source not a true outer-face site")
        events=[
            {"kind":"reaction","column":col,"point":source,"count":1},
            {"kind":"native_transport","source":source,
             "target":target,"species":product},
            {"kind":"outer_face_exchange","face":face,"point":source,
             "species":product,"direction":"inject","amount":2,
             "source_reference":"synthetic fixture; no empirical exchange rate"},
            {"kind":"outer_face_exchange","face":face,"point":source,
             "species":product,"direction":"extract","amount":3,
             "source_reference":"synthetic fixture; no empirical exchange rate"},
        ]
        final,ledger=run_original_spatial_event_history(
            initial,matrix,species,metadata,events)
        if (ledger["history_length"]!=4 or ledger["local_voxel_event_checks"]!=108
                or any(v<0 for v in final.values())):
            raise AssertionError("mixed source history failed")
        mixed_boundary_cases+=1
    transferred=0
    for origin,target in BONDS:
        for source,destination in ((origin,target),(target,origin)):
            for key in species:
                before=inventory(species)
                before[source,key]=1
                after=transport_event(before,species,source,destination,key,metadata)
                assert after[destination,key]==1
                transferred+=1
    result={
        "status":"source-reaction-identity-balanced-synthetic-event-rate",
        "original_3d_cube":[3,3,3],
        "source_species":len(species),
        "source_finite_reactions":len(original["reaction_index"]),
        "source_nonfinite_residuals":len(original["finite_formula_residuals"]),
        "original_reaction_event_checks":event_cases,
        "original_reaction_coordinate_checks":local_coordinate_checks,
        "original_mixed_face_reaction_history_checks":mixed_boundary_cases,
        "original_mixed_local_voxel_checks":mixed_boundary_cases*4*27,
        "original_reaction_transport_roundtrip_histories":mixed_history_cases,
        "original_native_bond_species_transfer_checks":transferred,
        "same_physical_shared_inventory":True,
        "source_CHNOP_and_signed_charge_balanced":True,
        "missing_original_external_exchange_never_inferred_zero":True,
        "original_29_exchange_rates_paid":False,
        "original_reaction_rate_measured":False,
        "original_membrane_permeability_measured":False,
        "physiological_tissue_evolution_validated":False,
        "agda_kernel_acceptance":False,
    }
    return result


def require_exact_flux_candidate_axes(original,candidate):
    """Reject missing, surplus or duplicated original quantitative axes.

    The existing feasibility checker intentionally reports missing axes as
    underdetermined; it may ignore surplus keys. Here, only reject surplus
    keys and malformed coordinate maps. Missing source-paid coordinates
    remain explicitly underdetermined in its existing tri-state result.
    """
    if not isinstance(candidate,dict):
        raise ValueError("original flux candidate must be an object")
    expected_reactions=set(original["reaction_index"])
    expected_species=set(original["species_index"])
    for name,expected in (("reaction_flux",expected_reactions),
                          ("external_exchange",expected_species)):
        coordinates=candidate.get(name)
        if not isinstance(coordinates,dict):
            raise ValueError(f"original {name} coordinate map required")
        extras=set(coordinates)-expected
        if extras:
            raise ValueError(
                f"original {name} has unrecognized source coordinates: "
                f"{sorted(extras)!r}")
        for key,value in coordinates.items():
            if isinstance(value,bool) or value is None:
                raise ValueError(f"invalid original {name} value for {key!r}")


def evaluate_source_paid_physical_candidate(certificate,parameters,candidate):
    """Reuse the existing original 29×12 flux/bound/exchange checker.

    A feasible algebraic S*v+e=0 candidate is *not* a dynamic physical
    update, compartment identification, validated transport rate, PNP
    model or causal hypothesis.
    """
    original,metadata=check_certificate(certificate,full_panel=True)
    require_exact_flux_candidate_axes(original,candidate)
    receipt=evaluate_original_flux_candidate(original,parameters,candidate)
    if receipt["reaction_count"]!=12 or receipt["species_count"]!=29:
        raise AssertionError("original source 29x12 matrix identity lost")
    if receipt["status"]!="feasible":
        return {"status":receipt["status"],
                "source_29x12_consistent":True,
                "physical_rate_validated":False,
                "missing_flux_bounds":receipt.get("missing_flux_bounds",[]),
                "missing_flux_values":receipt.get("missing_flux_values",[]),
                "missing_external_exchange":receipt.get("missing_external_exchange",[]),
                "candidate_flux_balance_witness":False}
    # Required for *referential* same-state provenance, not proof that
    # submitted numerical values were actually measured.
    if not all(isinstance(candidate.get(key),str) and
               candidate[key].strip() and
               "synthetic" not in candidate[key].lower()
               for key in ("same_state_reference","measurement_reference")):
        raise ValueError("flux candidate lacks source-specific same-state provenance")
    witness=receipt.get("candidate_flux_balance_witness")
    if witness is None:
        raise AssertionError("feasible result lacked its complete algebraic witness")
    return {"status":"feasible-algebraic-only",
            "source_29x12_consistent":True,
            "complete_12_reaction_flux_coordinates":True,
            "complete_29_environmental_exchange_coordinates":True,
            "candidate_flux_balance_witness":True,
            "same_state_reference":candidate["same_state_reference"],
            "measurement_reference":candidate["measurement_reference"],
            "physical_rate_validated":False,
            "transport_PNP_same_step_proved":False,
            "clinical_causality_proved":False}


def self_test():
    # One genuine, source-pinned RHEA:32253 directional QDPR reaction,
    # not a synthetic 29×12 panel or claim that all 29 rates are known.
    cert={"schema":"dashi.rhea-chebi-bh4-panel.v2",
          "reactions":[dict(QDPR, formula_charge_ready=True)]}
    result=test_source(cert,full_panel=False)
    assert result["source_species"]==5
    for duplicated in (
        '{"reaction_flux":{"RHEA:1":0,"RHEA:1":1}}',
        '{"external_exchange":{"species":0,"species":1}}',
        '{"reaction_flux":{"RHEA:1":NaN}}',
        '{"external_exchange":{"species":Infinity}}',
    ):
        try:
            load_original_receipt_json(duplicated)
        except ValueError:
            pass
        else:
            raise AssertionError("duplicate source or candidate JSON key admitted")
    assert result["source_finite_reactions"]==1
    assert result["original_reaction_event_checks"]==27
    assert result["original_reaction_coordinate_checks"]==27*27*5
    assert result["original_mixed_face_reaction_history_checks"]==1
    assert result["original_mixed_local_voxel_checks"]==108
    assert result["original_reaction_transport_roundtrip_histories"]==1
    assert result["original_native_bond_species_transfer_checks"]==540
    # Fail-closed negative controls: no fictional interior boundary,
    # no unreferenced environmental flux, and no extraction of material
    # that is not actually available in the selected cubical voxel.
    finite,metadata=check_certificate(cert,full_panel=False)
    key=next((candidate for candidate in finite["species_index"]
              if any(metadata[candidate][0][element] for element in ELEMENTS)
                 or metadata[candidate][1]!=0),None)
    if key is None:
        raise AssertionError("no source chemical quantity for local negative control")
    empty=inventory(finite["species_index"])
    for bad in (
        dict(face=(0,-1),point=(0,0,0),key=key,
             direction="inject",amount=1,source_reference="synthetic fixture"),
        dict(face=(0,-1),point=POINTS[0],key=key,
             direction="inject",amount=1,source_reference=""),
    ):
        try:
            boundary_species_event(empty,metadata,**bad)
        except ValueError:
            pass
        else:
            raise AssertionError("unpaid/nongeometric original exchange admitted")
    unchanged,ledger,actual=boundary_species_event(
        empty,metadata,face=(0,-1),point=POINTS[0],key=key,
        direction="extract",amount=100,source_reference="synthetic negative control")
    assert unchanged==empty and actual==0
    assert ledger==((0,)*len(ELEMENTS),0)
    # The original full-panel strict path additionally refuses invented
    # reaction/species keys. Exercise the pure coordinate guard against
    # the genuine one-column QDPR receipt without posing as a full panel.
    sample_axes={"reaction_index":finite["reaction_index"],
                 "species_index":finite["species_index"]}
    require_exact_flux_candidate_axes(sample_axes,
        {"reaction_flux":{},"external_exchange":{}})
    for wrong in (
        {"reaction_flux":{"RHEA:INVENTED":0},"external_exchange":{}},
        {"reaction_flux":{},"external_exchange":{"CHEBI:INVENTED":1}},
    ):
        try:
            require_exact_flux_candidate_axes(sample_axes,wrong)
        except ValueError:
            pass
        else:
            raise AssertionError("unrecognized original flux axis admitted")

    # Adversarial failure: moving a molecule between two original voxels
    # with no declared incidence current preserves global atoms/charge.
    # The *local* theorem must nevertheless detect this hidden transfer.
    displaced=empty.copy()
    source,target=BONDS[0]
    displaced[source,key]=2
    fake_before=displaced.copy()
    displaced[source,key]-=1
    displaced[target,key]+=1
    assert totals(displaced,metadata)==totals(fake_before,metadata)
    declared_div={point:[0]*6 for point in POINTS}
    declared_ext={point:[0]*6 for point in POINTS}
    try:
        assert_original_voxel_continuity(
            fake_before,displaced,metadata,declared_div,declared_ext,
            event_kind="adversarial undeclared remote redistribution")
    except AssertionError:
        pass
    else:
        raise AssertionError(
            "local signed/element continuity missed undeclared transport")
    print(json.dumps(result,indent=2,sort_keys=True))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate",type=Path)
    parser.add_argument("--self-test",action="store_true")
    parser.add_argument("--parameters",type=Path,
                        help="original source-qualified Rhea flux bounds")
    parser.add_argument("--candidate",type=Path,
                        help="complete original 12-flux/29-exchange candidate")
    args=parser.parse_args()
    if (args.parameters is None)!=(args.candidate is None):
        parser.error("--parameters and --candidate must be supplied together")
    if args.parameters is not None and args.certificate is None:
        parser.error("real original --certificate required with candidate flux")
    if args.certificate is not None:
        raw=args.certificate.read_bytes()
        certificate=load_original_receipt_json(raw)
        result=test_source(certificate,full_panel=True)
        result["original_certificate_sha256"]=hashlib.sha256(raw).hexdigest()
        if args.parameters is not None:
            parameters_bytes=args.parameters.read_bytes()
            candidate_bytes=args.candidate.read_bytes()
            result["original_flux_candidate"]=evaluate_source_paid_physical_candidate(
                certificate,
                load_original_receipt_json(parameters_bytes),
                load_original_receipt_json(candidate_bytes))
            result["strict_quantitative_input_receipt"]={
                "certificate_sha256":result["original_certificate_sha256"],
                "parameter_receipt_sha256":hashlib.sha256(parameters_bytes).hexdigest(),
                "candidate_receipt_sha256":hashlib.sha256(candidate_bytes).hexdigest(),
                "source_digest_independently_verified":False,
                "kinetic_measurements_independently_validated":False,
                "itir_pnf_promotion_performed":False,
            }
        print(json.dumps(result,indent=2,sort_keys=True))
        if args.parameters is not None and result["original_flux_candidate"]["status"] != "feasible-algebraic-only":
            raise SystemExit(2)
    elif args.self_test or args.certificate is None:
        self_test()


if __name__=="__main__":
    main()
