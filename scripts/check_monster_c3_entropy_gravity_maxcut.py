#!/usr/bin/env python3
"""Executable structural audit for the Monster/C3/entropy/gravity max-cut.

This is deliberately not an Agda proof or physical validation.  It checks the
exact arithmetic fixture and fail-closed source markers expected by the new
formal surfaces.  Agda typechecking remains a separate receipt.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, *needles: str) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            raise AssertionError(f"missing {needle!r} in {path}")


def main() -> None:
    residual53 = (3 + 3) * (3 ** (3 - 1)) - 1
    extended71 = (3 + 3 + (3 - 1)) * (3 ** (3 - 1)) - 1
    monster_degree_from_c3 = 53 + 3 * 65610
    monster_degree_from_ogg = 47 * 59 * 71

    assert residual53 == 53
    assert extended71 == 71
    assert monster_degree_from_c3 == 196883
    assert monster_degree_from_ogg == 196883
    assert 1 + monster_degree_from_c3 == 196884
    assert 1 + residual53 == 54

    require(
        "DASHI/Moonshine/MonsterC3ResidualTernaryArithmeticExact.agda",
        "residual53FromTernaryNeighbour",
        "ogg71FromExtendedTernaryNeighbour",
        "arithmeticIdentityProvesMonsterModuleIntertwiner",
        "arithmeticIdentityProvesGravity",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3EntropyStateCountingExact.agda",
        "degeneracyDeterminesProbabilityDistribution",
        "balancedCharacterCancellationMeansFineStatesAbsent",
        "coarseCancellationPreservesFineStateCount",
    )
    require(
        "DASHI/Physics/Closure/EntropyGravityIntertwinerBoundaryExact.agda",
        "scalarEntropyDensityDeterminesStressTensor",
        "entropyObservableAloneDerivesEinsteinDynamics",
        "jacobson1995LocalHorizonRoute",
        "padmanabhanNullEntropyDensityRoute",
    )
    require(
        "DASHI/Physics/Closure/MonsterGravityAuthorityAndDimensionExact.agda",
        "https://arxiv.org/abs/0706.3359",
        "https://arxiv.org/abs/2008.06742",
        "https://arxiv.org/abs/gr-qc/9504004",
        "https://arxiv.org/abs/1505.04753",
        "https://arxiv.org/abs/1012.0119",
    )
    require(
        "DASHI/Physics/Closure/Monster3Plus1PhysicalSymmetryTargetExact.agda",
        "monsterIsSymmetryOfObserved3Plus1Universe",
        "statusMeansUnpaidNotImpossible",
        "missingNovelQuantitativePrediction",
        "missingIndependentEmpiricalValidation",
    )
    require(
        "DASHI/Physics/Chemistry/AtomicPeriodicTable369C3EntropyIntertwinerExact.agda",
        "global369TernaryEncodingImpliesMolecularC3Symmetry",
        "c3MolecularSectorImpliesMonsterModule",
        "molecularEntropyImpliesPhysicalGravity",
        "concreteSameObjectC3MoleculeInstantiated",
    )

    print("monster/C3/entropy/gravity max-cut structural audit: ok")
    print(f"53 fixture: {residual53}")
    print(f"71 fixture: {extended71}")
    print(f"Monster degree via C3: {monster_degree_from_c3}")
    print(f"Monster degree via Ogg factors: {monster_degree_from_ogg}")


if __name__ == "__main__":
    main()
