#!/usr/bin/env python3
"""Hardt × Brain-IT × dashiBRAIN: intervention identifiability max-cut.

A standard-library finite structural causal model. No real human EEG,
fMRI, MEG, Drosophila or occult target data is loaded. All claims are
conditional on the declared toy models. Optional reuse of the *original*
dashiBRAIN #9 consumer-retention runtime is explicit, not vendored.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from pathlib import Path
from collections import defaultdict
import argparse
import importlib.util
import json
import hashlib


@dataclass(frozen=True)
class World:
    common_cue: int
    mechanism: str
    image: int = 0
    secret: int = 0


def candidates():
    return tuple(World(c, m, i, t) for c, m, i, t in product(
        (0, 1), ("direct", "common_cause"), (0, 1), (0, 1)))


def passive(w: World):
    # Observational stimulus/outcome: X=U and Y=U in BOTH causal worlds.
    return (w.common_cue, w.common_cue, w.image)


def intervene(w: World, force: int):
    # In direct model, Y:=do(X); in confounded world, Y:=U.
    return force if w.mechanism == "direct" else w.common_cue


def contrast(w: World):
    return (intervene(w, 0), intervene(w, 1))


def audit_by_fibre(states, observe, consumer):
    seen = {}
    ambiguous = set()
    witness = None
    for w in states:
        q, y = observe(w), consumer(w)
        if q in seen and seen[q][1] != y:
            ambiguous.add(q)
            if witness is None:
                witness = (seen[q][0], w)
        else:
            seen.setdefault(q, (w, y))
    return {"factorises":not ambiguous,
            "fibre_count":len(seen),
            "ambiguous_fibres":len(ambiguous),
            "witness":witness}


def causal_collision():
    worlds=candidates()
    obs=audit_by_fibre(worlds,passive,contrast)
    assert not obs["factorises"]
    assert obs["witness"] is not None
    a,b=obs["witness"]
    assert passive(a)==passive(b) and contrast(a)!=contrast(b)
    # Counterexample to closed coarse dynamics under an intervention:
    # passive coarse observation is identical, but post-intervention Y differs.
    matching=next((a,b) for a,b in product(worlds,repeat=2)
         if a.common_cue==b.common_cue==0 and a.image==b.image==0 and
         a.secret==b.secret==0 and
         a.mechanism=="direct" and b.mechanism=="common_cause")
    x,y=matching
    assert passive(x)==passive(y)
    assert intervene(x,1)==1 and intervene(y,1)==0
    assert all(passive(World(u,"direct",im,t))==
               passive(World(u,"common_cause",im,t))
               for u,im,t in product((0,1),repeat=3))
    return {"worlds":len(worlds),
            "passive_observation_fibres":obs["fibre_count"],
            "intervention_ambiguous_fibres":obs["ambiguous_fibres"],
            "perfect_observational_agreement_with_different_do_effect":True,
            "same_passive_state_has_different_intervention_response":True,
            "no_closed_coarse_intervention_transition":True,
            "scope":"finite SCM, not a human causal experiment"}


def concealed_target_collision():
    worlds=candidates()
    viewed=audit_by_fibre(worlds,lambda w:w.image,lambda w:w.image)
    target=audit_by_fibre(worlds,lambda w:w.image,lambda w:w.secret)
    leaked=audit_by_fibre(worlds,lambda w:(w.image,w.secret),lambda w:w.secret)
    assert viewed["factorises"] and not target["factorises"] and leaked["factorises"]
    return {"viewed_image_consumer_retained":True,
            "independent_secret_not_recoverable":True,
            "leaked_secret_decodable":True,
            "scope":"toy viewed image/independent concealed target, not Brain-IT NSD results"}


def modality_receipt_fail_closed():
    # An experimental result must preserve subject, modality, timebase,
    # physical source and intervention. Human fMRI, human delta EEG and
    # fly calcium/structural connectome are not interchangeable data.
    @dataclass(frozen=True)
    class Modal:
        species:str; modality:str; sampling:str; source:str
    brainit=Modal("human","BOLD-fMRI","hemodynamic","Beliy et al ICLR 2026")
    delta=Modal("human","scalp-EEG","electrical","source-unknown")
    fly=Modal("Drosophila","calcium-imaging","fluorescence","MaleCNS donor")
    diamond=Modal("human","cardiac-MCG","magnetic","Omar et al 2026")
    assert len({brainit,delta,fly,diamond})==4
    def same_physical_measure(a,b):
        return a.species==b.species and a.modality==b.modality and a.sampling==b.sampling and a.source==b.source
    assert not any(same_physical_measure(a,b) for a,b in
                   product((brainit,delta,fly,diamond),repeat=2) if a!=b)
    return {"wrong_type_mappings_rejected":6,
            "brainit_fmri_not_delta_eeg":True,
            "fly_calcium_not_human_neural_field":True,
            "cardiac_diamond_mcg_not_brain_neural_source":True,
            "scope":"semantic receipt gating only"}


def optional_brain_runtime(path):
    if path is None:
        return {"status":"NOT_IMPORTED","reason":"dashiBRAIN #9 file not present locally; no vendoring"}
    path=Path(path)
    raw=path.read_bytes()
    observed_blob=hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()
    expected_blob="384a9b1d7082857000128635259c9b1a9d989f80"
    if observed_blob != expected_blob:
        raise ValueError("dashiBRAIN original runtime blob mismatch: "+observed_blob)
    spec=importlib.util.spec_from_file_location("external_brain_consumer_retention",path)
    if spec is None or spec.loader is None:
        raise ValueError(f"Cannot load external original runtime: {path}")
    import sys
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    worlds=candidates()
    original=module.audit_consumer_retention(worlds,passive,contrast)
    local=audit_by_fibre(worlds,passive,contrast)
    assert original.factorises_on_sample == local["factorises"]
    assert original.fibre_count == local["fibre_count"]
    assert original.ambiguous_fibre_count == local["ambiguous_fibres"]
    assert original.collision is not None
    # Reuse the ORIGINAL dashiBRAIN commutation audit, too. One physically
    # declared active intervention cannot be a state-independent function
    # of the passive quotient when mechanisms share the observation.
    states=[(w,passive(w)) for w in worlds]
    def fine_step(pair):
        w,q=pair
        return (w,(q[0],intervene(w,1),q[2]))
    comm=module.audit_commutation(states,fine_step,lambda pair:pair[1],
                                  lambda q:q)
    assert comm.state_count==16 and comm.mismatches==4
    return {"status":"ORIGINAL_RUNTIME_REUSED", "original_path":str(path),
            "factorises":original.factorises_on_sample,
            "ambiguous_fibres":original.ambiguous_fibre_count,
            "sham_coarse_step_mismatches":comm.mismatches,
            "official_source_git_blob_verified":True,
            "source_git_blob_sha1":observed_blob}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--brain-runtime",default=None,
                        help="path to original dashiBRAIN PR9 consumer_retention.py")
    args=parser.parse_args()
    result={"status":"EXACT_FINITE_SYNTHETIC_ONLY",
            "causal":causal_collision(),
            "brainit":concealed_target_collision(),
            "modality":modality_receipt_fail_closed(),
            "brain_runtime":optional_brain_runtime(args.brain_runtime)}
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__=="__main__":
    main()
