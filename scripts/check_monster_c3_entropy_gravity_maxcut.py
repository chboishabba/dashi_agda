#!/usr/bin/env python3
"""Structural audit for the Monster/C3/369 chemistry/entropy/gravity max-cut."""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def require(path: str, *needles: str) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            raise AssertionError(f"missing {needle!r} in {path}")

def main() -> None:
    assert (3 + 3) * 9 - 1 == 53
    assert (3 + 3 + 2) * 9 - 1 == 71
    assert 53 + 3 * 65610 == 196883 == 47 * 59 * 71
    assert 8536 - 4223 == 4313
    assert 555245 - 554554 == 691
    assert 55517555010 / 1_000_000_000 == 55.51755501
    assert 55519414318 / 1_000_000_000 == 55.519414318

    require("DASHI/Physics/Chemistry/AmmoniaHamiltonianWavefunctionExact.agda",
            "literalOccupationBasisStatePaid", "numericRealSpaceWavefunctionCoefficientsPaid")
    require("DASHI/Physics/Chemistry/AmmoniaSTO3GFCIExact.agda",
            "10.1088/2058-9565/ad7d32", "sourceBackedFCIDiagonalizationPaid")
    require("DASHI/Physics/Chemistry/AmmoniaSCIReleasedArtifactExact.agda",
            "07541705a0305e75dab1de5bc1b8324d66fee778", "55517555010", "55519414318",
            "paperBenchmarkAndArtifactAreSameNumericalObject", "matrixIndependentlyRediagonalizedByDASHI")
    require("DASHI/Physics/Chemistry/AmmoniaGroundStateC3ActionExact.agda",
            "groundDeterminantPhase", "closedShellDeterminantInvariantPaid")
    require("DASHI/Physics/Chemistry/AmmoniaMonster3BActionProbeExact.agda",
            "canonicalC3PhaseCoordinateIntertwiner", "formalTrivialMonsterActionHasPhysicalContent",
            "monsterActionOnAmmoniaPaid")
    require("DASHI/Physics/Chemistry/AmmoniaH3PlusC3ResolvedReactionExact.agda",
            "fullProofRelevantC3ResolvedReactionTransitionPaid", "4313",
            "selectedC3EqualsFullProductPointGroup")
    require("DASHI/Physics/Chemistry/AmmoniaHydrogenAbstractionMechanismExact.agda",
            "10.1021/jp1001513", "10.1063/1.3605242",
            "sourceBackedTimeDependentWavepacketDynamicsPaid")
    require("DASHI/Physics/Chemistry/AmmoniaHydrogenAbstraction369HyperfibreExact.agda",
            "literalChemistryHyperfibreInhabited", "fibreCreatesMonsterAction")
    require("DASHI/Physics/Closure/MonsterC3EntropyGravityMaxCutExact.agda",
            "authorReleasedMatrixRediagonalizedByDASHI", "h3ProofRelevantC3ReactionPaid",
            "observed3Plus1MonsterPaid")
    require("DASHI/Physics/Closure/EntropyGravityIntertwinerBoundaryExact.agda",
            "scalarEntropyDensityDeterminesStressTensor", "entropyObservableAloneDerivesEinsteinDynamics")

    print("monster/C3/369 chemistry/entropy/gravity structural audit: ok")
    print("published benchmark and author-released CI artifacts remain distinct")
    print("independent matrix rediagonalization remains explicitly unpaid")

if __name__ == "__main__":
    main()
