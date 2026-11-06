#!/usr/bin/env python3
"""Y443 finite-transcription regression and optional golden Agda gate.

The finite check validates Ivanov/Bray/TauCeti source transcription arithmetic;
it does not prove a Monster isomorphism, JMD's two-generator certificate,
or an actual automorphism action. The default gate ALSO runs Agda and fails
if no compiler is available. --finite-only is explicitly non-promotional.
"""
from __future__ import annotations

import argparse
from itertools import combinations
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PRESENTATION = ROOT / "DASHI/Moonshine/Y443CoxeterPresentationExact.agda"
ACTION = ROOT / "DASHI/Moonshine/Y443VNaturalPairGenerationExact.agda"
TRACE = ROOT / "DASHI/Moonshine/Y443JMDTracePowerExact.agda"
HEISENBERG = ROOT / "DASHI/Moonshine/Y443Monster3BTwelveDisjointExact.agda"
ORBIT = ROOT / "DASHI/Moonshine/Y443ArmSwapOrbitMaxCutExact.agda"
INDEXED = ROOT / "DASHI/Moonshine/Y443Relator72IndexedBidiExact.agda"

NODES = ("a", "b1", "c1", "d1", "e1", "b2", "c2", "d2", "e2", "b3", "c3", "d3")
EDGES = {
    frozenset((x, y)) for x, y in (
        ("a", "b1"), ("b1", "c1"), ("c1", "d1"), ("d1", "e1"),
        ("a", "b2"), ("b2", "c2"), ("c2", "d2"), ("d2", "e2"),
        ("a", "b3"), ("b3", "c3"), ("c3", "d3"),
    )
}
SPIDER = ("a", "b1", "c1", "a", "b2", "c2", "a", "b3", "c3")
CENTRAL = ("a", "b3", "c3", "d3", "b1", "c1", "b2")


def assert_finite_counts() -> None:
    pairs = list(combinations(NODES, 2))
    adjacent = [p for p in pairs if frozenset(p) in EDGES]
    nonadjacent = [p for p in pairs if frozenset(p) not in EDGES]
    assert (len(NODES), len(pairs), len(adjacent), len(nonadjacent)) == (12, 66, 11, 55)

    # Relators are positive words because x^2=1 for each Coxeter node.
    coxeter = [(x, x) for x in NODES]
    coxeter += [
        tuple(p) * (3 if frozenset(p) in EDGES else 2)
        for p in pairs
    ]
    spider_word = SPIDER * 10
    central_word = CENTRAL * 9
    double = coxeter + [spider_word]
    monster = double + [central_word]

    assert (len(coxeter), len(double), len(monster)) == (78, 79, 80)
    assert (len(spider_word), len(central_word)) == (90, 63)
    assert (sum(map(len, coxeter)), sum(map(len, double)),
            sum(map(len, monster))) == (310, 400, 463)
    assert SPIDER == ("a", "b1", "c1", "a", "b2", "c2", "a", "b3", "c3")
    assert CENTRAL == ("a", "b3", "c3", "d3", "b1", "c1", "b2")
    print("PASS finite: 12 nodes / 11 edges / 55 nonedges / 78,79,80 relators / 310,400,463 letters")


def assert_source_scope() -> None:
    for file in (PRESENTATION, ACTION, TRACE, HEISENBERG, ORBIT, INDEXED):
        if not file.is_file():
            raise AssertionError(f"missing Agda source: {file}")
        source = file.read_text()
        for forbidden in (
            "postulate\n", "{!", "!}", "--allow-unsolved-metas",
            "--no-termination-check", "--no-positivity-check", "--unsafe",
        ):
            if forbidden in source:
                raise AssertionError(f"forbidden trust escape {forbidden!r} in {file.name}")
    a = PRESENTATION.read_text()
    b = ACTION.read_text()
    for symbol in (
        "elevenEdges", "fiftyFiveNonedges", "coxeterRelatorCount",
        "doubleMonsterRelatorCount", "monsterRelatorCount",
        "doubleMonsterWrittenLength", "monsterWrittenLength",
        "centralInvolutionRelator",
    ):
        if symbol not in a:
            raise AssertionError(f"missing presentation theorem {symbol}")
    for symbol in (
        "pairWordsSurjective", "pairWordActionMatchesLiteral",
        "NodeWordCertificate", "NodeGeneration",
        "RelatorsSatisfied", "VN.VNaturalConstruction",
    ):
        if symbol not in b:
            raise AssertionError(f"missing action theorem {symbol}")
    t = TRACE.read_text()
    for symbol in ("powerRepresented", "traceStepThreeX4", "traceStepFourBeta", "traceStepsThreeAndFour"):
        if symbol not in t:
            raise AssertionError(f"missing JMD trace theorem {symbol}")
    h = HEISENBERG.read_text()
    for symbol in ("axis0DoubleTranslationIsNotIdentity", "axis0TripleTranslationIsIdentity", "axis0TripleTranslationEverywhere"):
        if symbol not in h:
            raise AssertionError(f"missing order-3/order-2 disjointness theorem {symbol}")
    for source, symbols in ((ORBIT, ("swapPreservesAdjacency", "fixedNonedgesAreSeven", "coreIsEightByNine", "fullCutIsSeventyTwoPlusEight")), (INDEXED, ("allTagsRecoverOriginal80Words", "coxeterCoreCount", "fullResidualCount"))):
        txt = source.read_text()
        for symbol in symbols:
            if symbol not in txt:
                raise AssertionError(f"missing Y443 orbit/indexed theorem {symbol} in {source.name}")
    print("PASS source: Y443 72+8 indexed relation algebra and JMD proofs without listed trust escapes")


def check_agda() -> None:
    compiler = os.environ.get("AGDA_BIN", "agda")
    if not shutil.which(compiler):
        raise RuntimeError(
            f"Golden Agda NOT RUN: {compiler!r} not found; "
            "finite-only must not be cited as kernel acceptance"
        )
    flags = ["--safe", "-i", ".", "-l", "standard-library"]
    for file in (PRESENTATION, ACTION):
        print(f"Agda checking: {file.relative_to(ROOT)}", flush=True)
        subprocess.run(
            [compiler, *flags, str(file.relative_to(ROOT))],
            cwd=ROOT, check=True,
        )
    print("PASS golden Agda: both Y443 modules typechecked")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--finite-only", action="store_true",
                        help="run source arithmetic only; NOT a proof promotion")
    args = parser.parse_args()
    assert_finite_counts()
    assert_source_scope()
    if args.finite_only:
        print("STATUS: finite-only / Agda NOT RUN / Y443 group isomorphism NOT CLAIMED")
    else:
        check_agda()
        print("STATUS: finite exact cut Agda-accepted; JMD witness still not imported")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
