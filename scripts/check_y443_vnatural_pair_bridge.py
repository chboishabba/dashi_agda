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
NOGO = ROOT / "DASHI/Moonshine/Y443Nonary72EquivarianceNoGoExact.agda"
JMD_SOURCE = ROOT / "DASHI/Moonshine/Y443JMDSourceWordInstantiationExact.agda"
JMD_COMPILER = ROOT / "DASHI/Moonshine/Y443JMDConcretePairPowerCompilerExact.agda"

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

    # Independent C2 graph automorphism census: swap the two long arms.
    swap = {n: (n[:-1] + "2" if n.endswith("1")
                else n[:-1] + "1" if n.endswith("2") else n)
            for n in NODES}
    assert all(swap[swap[n]] == n for n in NODES)
    assert all((frozenset((swap[a], swap[b])) in EDGES)
               == (frozenset((a, b)) in EDGES) for a, b in pairs)
    fixed_nodes = [n for n in NODES if swap[n] == n]
    fixed_pairs = [p for p in pairs
                   if frozenset(p) == frozenset((swap[p[0]], swap[p[1]]))]
    fixed_edges = [p for p in fixed_pairs if frozenset(p) in EDGES]
    fixed_nonedges = [p for p in fixed_pairs if frozenset(p) not in EDGES]
    assert (len(fixed_nodes), len(fixed_pairs),
            len(fixed_edges), len(fixed_nonedges)) == (4, 10, 3, 7)
    moving_nodes = [n for n in NODES if swap[n] != n]
    moving_edges = [p for p in adjacent if p not in fixed_edges]
    moving_nonedges = [p for p in nonadjacent if p not in fixed_nonedges]
    assert (len(moving_nodes), len(moving_edges),
            len(moving_nonedges)) == (8, 8, 48)

    # The canonical 72 block is ALL 55 nonedges + 8 moving nodes
    # + 8 moving edge relators + the UNIQUE trivalent central node a.
    core = ([("nonedge", p) for p in nonadjacent]
            + [("square", n) for n in moving_nodes]
            + [("edge", p) for p in moving_edges]
            + [("square", "a")])
    residual = ([("square", n) for n in ("b3", "c3", "d3")]
                + [("edge", p) for p in fixed_edges]
                + [("spider", None), ("central", None)])
    assert len(core) == 72 and len(residual) == 8
    alltags = ([("square", n) for n in NODES]
               + [("edge" if frozenset(p) in EDGES else "nonedge", p)
                  for p in pairs]
               + [("spider", None), ("central", None)])
    assert set(core).isdisjoint(residual)
    assert set(core) | set(residual) == set(alltags)
    assert len(alltags) == len(set(alltags)) == 80
    assert len(fixed_edges) == 3 and len(fixed_nonedges) == 7
    assert 78 == 72 + 6 and 80 == 72 + 8
    # This C2 quotient has 7 edge-orbits, 31 nonedge-orbits:
    # NOT the 5 classes of 9, nor the 14 classes of 27.
    assert len(fixed_edges) + len(moving_edges) // 2 == 7
    assert len(fixed_nonedges) + len(moving_nonedges) // 2 == 31
    print("PASS arm-swap: fixed (node,edge,nonedge)=(4,3,7); moving=(8,8,48)")
    print("PASS canonical Y443: all 55 nonedges +8 nodes +8 edges +centre=72; residual=8")

    print("PASS finite: 12 nodes / 11 edges / 55 nonedges / 78,79,80 relators / 310,400,463 letters")


def assert_source_scope() -> None:
    for file in (PRESENTATION, ACTION, TRACE, HEISENBERG, ORBIT, INDEXED, NOGO, JMD_SOURCE, JMD_COMPILER):
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
    no_go = NOGO.read_text()
    for symbol in ("centralCoreFixed", "reducedEightHasNoFixedPoint", "chartHasNoFixedPoint", "noNaiveEightByNineEquivariantChart"):
        if symbol not in no_go:
            raise AssertionError(f"missing Y443 8x9 equivariance no-go {symbol}")
    for source, symbols in ((JMD_SOURCE, ("uPathHasEight", "betaPathHasFour", "thirdPathHasFive", "wIsX4Beta", "jmdWFromPair")), (JMD_COMPILER, ("concreteTrace", "sourceX4Word", "sourceBetaWord"))):
        src = source.read_text()
        for symbol in symbols:
            if symbol not in src:
                raise AssertionError(f"missing JMD source theorem {symbol}")
    print("PASS source: real JMD u/v words and concrete pair-power compiler included")


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
