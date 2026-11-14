#!/usr/bin/env python3
"""Deterministic fail-closed mutation controls for the eta source receipt.

No GitHub/API, network, native toolchain, or mathematical inference.
Tests that a manifest cannot turn source co-location into a kernel,
dyadic-analytic or RH acceptance, or silently lose a donor blob/import.
"""
import copy
import json

from check_bishop_eta_source_transfer_receipt import (
    RECEIPT, Blocked, verify_receipt,
)

def run():
    trusted = json.loads(RECEIPT.read_text(encoding="utf-8"))
    base = verify_receipt(trusted)
    assert base["copied_source_blobs"] == 10
    assert base["immediate_dashi_imports"] == 31
    assert base["kernel_accepted"] is False
    assert base["local_objects_checked"] is False

    cases = [
        ("kernel_promotion",
         lambda x: x.update(local_agda29_kernel_accepted=True)),
        ("dyadic_promotion",
         lambda x: x.update(original_dyadic_term_identity_proved=True)),
        ("eta_tail_promotion",
         lambda x: x.update(compact_uniform_eta_convergence_proved=True)),
        ("RH_promotion",
         lambda x: x.update(clay_or_rh_theorem_proved=True)),
        ("full_import_elaboration_promotion",
         lambda x: x.update(all_imports_elaborated=True)),
        ("omitted_blob",
         lambda x: x["copied_source_blobs"].pop()),
        ("duplicate_blob",
         lambda x: x["copied_source_blobs"].__setitem__(
             1, copy.deepcopy(x["copied_source_blobs"][0]))),
        ("invalid_blob_sha",
         lambda x: x["copied_source_blobs"][0].update(blob_sha="0" * 39)),
        ("invalid_path",
         lambda x: x["copied_source_blobs"][0].update(path="../poison.agda")),
        ("missing_immediate_import",
         lambda x: x["other_immediate_dashi_imports_present"].pop()),
        ("duplicate_immediate_import",
         lambda x: x["other_immediate_dashi_imports_present"].__setitem__(
             1, x["other_immediate_dashi_imports_present"][0])),
        ("false_cross_source_owner",
         lambda x: x.update(new_same_term_owner="DASHI/Analysis/Invented.agda")),
        ("wrong_recipient",
         lambda x: x.update(recipient_pr=1408)),
        ("same_source_and_recipient",
         lambda x: x.update(recipient_head=x["source_head"])),
        ("false_status",
         lambda x: x.update(source_status="kernel_accepted")),
    ]
    for name, mutation in cases:
        trial = copy.deepcopy(trusted)
        mutation(trial)
        try:
            verify_receipt(trial)
        except Blocked:
            continue
        raise AssertionError("fail-open receipt under " + name)
    print(f"PASS: {len(cases)}/{len(cases)} negative fail-closed receipt controls")
    print("PASS: 10 recorded donor blobs and 31 immediate import paths")
    print("NO kernel proof or mathematical source theorem accepted")

if __name__ == "__main__":
    run()
