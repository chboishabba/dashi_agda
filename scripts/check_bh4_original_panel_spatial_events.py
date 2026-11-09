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

ROOT=Path(__file__).resolve().parents[1]
CANONICAL_OWNER=ROOT/"DASHI/Biology/Molecular/BH4ExecutedPanelReactionReceiptExact.agda"
POINTS=tuple(product((-1,0,1),repeat=3))
BONDS=tuple((p,tuple(p[i]+int(i==axis) for i in range(3)))
       for p in POINTS for axis in range(3) if p[axis]<1)
assert len(POINTS)==27 and len(BONDS)==54
ELEMENTS=("C","H","N","O","P")


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


def self_test():
    # One genuine, source-pinned RHEA:32253 directional QDPR reaction,
    # not a synthetic 29×12 panel or claim that all 29 rates are known.
    cert={"schema":"dashi.rhea-chebi-bh4-panel.v2",
          "reactions":[dict(QDPR, formula_charge_ready=True)]}
    result=test_source(cert,full_panel=False)
    assert result["source_species"]==5
    assert result["source_finite_reactions"]==1
    assert result["original_reaction_event_checks"]==27
    assert result["original_reaction_coordinate_checks"]==27*27*5
    assert result["original_reaction_transport_roundtrip_histories"]==1
    assert result["original_native_bond_species_transfer_checks"]==540
    print(json.dumps(result,indent=2,sort_keys=True))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate",type=Path)
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    if args.certificate is not None:
        raw=args.certificate.read_bytes()
        result=test_source(json.loads(raw),full_panel=True)
        result["original_certificate_sha256"]=hashlib.sha256(raw).hexdigest()
        print(json.dumps(result,indent=2,sort_keys=True))
    elif args.self_test or args.certificate is None:
        self_test()


if __name__=="__main__":
    main()
