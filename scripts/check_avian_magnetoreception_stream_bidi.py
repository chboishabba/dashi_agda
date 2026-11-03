#!/usr/bin/env python3
"""DASHI-only source-contract audit for bird magnetoreception cross-pollination.

This checks source/attribution/owner wiring, not Agda kernel correctness,
causal biological mechanism or safe genetic editing. --agda attempts real
type-checking and fails if the Agda executable is absent.

The Thought Emporium (17 June 2020) retains authorship of the video.
Nimpf, Xu, Nordmann, Wang, Lisowski et al. retain experimental attribution.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path
from typing import Mapping

ROOT = Path(__file__).resolve().parents[1]
CORE = "DASHI/Biology/AvianMagnetoreceptionStreamFiniteCore.agda"
ADAPTER = "DASHI/Biology/AvianMagnetoreceptionThoughtEmporiumEvidenceExact.agda"
DOC = "docs/biology/ThoughtEmporiumAvianMagnetoreceptionCrosswalk.md"
BIO_ROOT = "DASHI/Biology/Everything.agda"
TOE_ROOT = "DASHI/Everything.agda"
EXISTING = (
    "DASHI/Biology/MagnetoreceptionSurface.agda",
    "DASHI/Biology/AvianCryptochromeMagnetoreceptionInhabitant.agda",
    "DASHI/Biology/AvianHepaticMacrophageMagnetoreception.agda",
    "DASHI/Biology/AvianMagnetoreceptionSourceRegistry.agda",
    "DASHI/Biology/AvianRFOverlayMechanismAdapter.agda",
)
FILES = (CORE, ADAPTER, DOC, BIO_ROOT, TOE_ROOT) + EXISTING
AGDA = (CORE, ADAPTER, BIO_ROOT, TOE_ROOT)

REQUIRED = {
    CORE: (
        "{-# OPTIONS --safe #-}",
        "data Mechanism",
        "data AssayTransport",
        "data CrossSpeciesTransport",
        "constantFluxNotChangingFlux",
        "stationaryConstantFluxDoesNotSupplyInductionPremise",
        "videoDoesNotProveHumanGain",
        "mechanismProposalDoesNotProveHumanGain",
        "humanEEGNotHumanGeneticEnhancement",
        "pigeonObservationNotHumanGain",
        "robinInVitroNotHumanGain",
        "cryptochromeInVitroNotHomingBehavior",
        "oneMechanismNotExclusive",
    ),
    ADAPTER: (
        "The Thought Emporium",
        "2020-06-17",
        "10.1016/j.cub.2019.09.048",
        "10.1038/s41586-021-03618-9",
        "10.1126/science.aea6425",
        "10.1126/science.ady2486",
        "10.1523/ENEURO.0483-18.2019",
        "import DASHI.Core.AttributedSourceCore as Source",
        "import DASHI.Core.ScientificMechanismEvidenceBidiExact as Science",
        "import DASHI.Biology.MagnetoreceptionSurface as Generic",
        "import DASHI.Biology.AvianCryptochromeMagnetoreceptionInhabitant as CRY",
        "import DASHI.Biology.AvianHepaticMacrophageMagnetoreception as Hepatic",
        "import DASHI.Biology.AvianMagnetoreceptionSourceRegistry as Registry",
        "import DASHI.Biology.AvianRFOverlayMechanismAdapter as RF",
        "CRY.cryptochromeGenericSurface",
        "Hepatic.hepaticMacrophageGenericSurface",
        "Registry.lisowskiEtAl2026",
        "Generic.vestibularCandidateChannel",
        "Generic.vestibularCandidateRoute",
        "RF.canonicalAvianRFOverlayMechanismAdapter",
        "singleCompetingMechanismProvenIsFalse",
        "causalHumanGeneTransferPaidIsFalse",
        "citationDoesNotImportTheorem = refl",
    ),
    DOC: (
        "59388d04a5e7baa3465f84bcf25d71830e9e5d61c3ebc011d7c8ca05fda758c8",
        "M01",
        "M08",
        "Lisowski",
        "Nordmann",
        "Nimpf",
        "The Thought Emporium",
        "No tested animal or human genetic gain of function",
    ),
    BIO_ROOT: (
        "import DASHI.Biology.AvianMagnetoreceptionStreamFiniteCore",
        "import DASHI.Biology.AvianMagnetoreceptionThoughtEmporiumEvidenceExact",
    ),
    TOE_ROOT: (
        "import DASHI.Biology.AvianMagnetoreceptionStreamFiniteCore",
        "import DASHI.Biology.AvianMagnetoreceptionThoughtEmporiumEvidenceExact",
    ),
    EXISTING[0]: ("vestibularCandidateChannel", "hepaticMacrophageChannel", "radicalPairRetinalChannel"),
    EXISTING[1]: ("cryptochromeGenericSurface", "cryptochromeMechanismExclusiveIsFalse"),
    EXISTING[2]: ("hepaticMacrophageGenericSurface", "afferentMechanismDirectlyEstablishedIsFalse"),
    EXISTING[3]: ("lisowskiEtAl2026", "10.1126/science.ady2486"),
    EXISTING[4]: ("canonicalAvianRFOverlayMechanismAdapter", "genericRFDisruptionProvesRadicalPairMechanismIsFalse"),
}

BAD_AGDA = (
    re.compile(r"^\s*postulate\b", re.MULTILINE),
    re.compile(r"\{\-#\s*(?:TERMINATING|NON_TERMINATING)\b"),
    re.compile(r"\{\![\s\S]*?\!\}"),
    re.compile(r"--allow-unsolved-metas|--type-in-type|--no-positivity-check"),
)

def load_sources(root: Path = ROOT) -> dict[str, str]:
    return {
        p: (root / p).read_text(encoding="utf-8")
        for p in FILES if (root / p).is_file()
    }


def inspect_source_contract(sources: Mapping[str, str]) -> list[str]:
    failures: list[str] = []
    for path, required in REQUIRED.items():
        value = sources.get(path)
        if value is None:
            failures.append(f"missing source: {path}")
            continue
        for marker in required:
            if marker not in value:
                failures.append(f"missing marker {marker} in {path}")
    if CORE in sources:
        core = sources[CORE]
        if not core.startswith("{-# OPTIONS --safe #-}"):
            failures.append("Golden finite core is not safe")
        for symbol in ("postulate", "{-# TERMINATING"):
            if symbol in core:
                failures.append(f"unsafe Golden source: {symbol}")
    for path in (CORE, ADAPTER):
        if path not in sources:
            continue
        for pattern in BAD_AGDA:
            if pattern.search(sources[path]):
                failures.append(f"trust escape in {path}: {pattern.pattern}")
    if ADAPTER in sources:
        adapter = sources[ADAPTER]
        if adapter.startswith("{-# OPTIONS --safe #-}"):
            failures.append("legacy owner adapter must not claim an all-safe import graph")
        for semantic in (
            "Science.sourceInterpretation",
            "Science.preliminary",
            "Science.experimentalObservation",
            "Science.sourceBacked",
            "Generic.structuralHypothesis",
            "Generic.correlationalReceipt",
        ):
            if semantic not in adapter:
                failures.append(f"missing evidence-ceiling guard: {semantic}")
    if DOC in sources:
        doc = sources[DOC]
        if "No tested animal or human genetic gain of function" not in doc:
            failures.append("transcript scientific ceiling lost")
        if "M05" not in doc:
            failures.append("human evidence/cross-species cut lost")
    return failures


def run_agda(root: Path = ROOT) -> dict:
    agda = shutil.which("agda")
    if agda is None:
        return {"state": "unavailable", "passed": False, "reason": "Agda not installed"}
    results = []
    for path in AGDA:
        try:
            p = subprocess.run([agda, "-i", ".", path], cwd=root,
                               text=True, capture_output=True, timeout=240)
            results.append({"path": path, "passed": p.returncode == 0,
                            "returncode": p.returncode,
                            "output_tail": (p.stdout + p.stderr)[-1200:]})
            if p.returncode:
                break
        except subprocess.TimeoutExpired:
            results.append({"path": path, "passed": False, "reason": "timeout"})
            break
    return {"state": "executed", "passed": len(results) == len(AGDA)
            and all(x["passed"] for x in results), "results": results}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--agda", action="store_true",
                        help="Require and run real focused Agda checks")
    args = parser.parse_args()
    failures = inspect_source_contract(load_sources())
    receipt = {
        "schema": "dashi.avian-magnetoreception-evidence.v1",
        "scope": "DASHI source-attributed science only, no genome editing implementation",
        "video_transcript_sha256": "59388d04a5e7baa3465f84bcf25d71830e9e5d61c3ebc011d7c8ca05fda758c8",
        "static_contract_passed": not failures,
        "static_failures": failures,
        "biological_mechanisms_exclusively_resolved": False,
        "human_genetic_enhancement_demonstrated": False,
        "agda": {"state": "not_requested", "passed": False},
    }
    if args.agda and not failures:
        receipt["agda"] = run_agda(ROOT)
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0 if not failures and (not args.agda or receipt["agda"]["passed"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
