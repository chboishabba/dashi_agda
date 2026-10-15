#!/usr/bin/env python3
"""Structural audit for the Monster/C3/369 chemistry/entropy/gravity max-cut.

Not an Agda proof or physical validation. It checks exact finite arithmetic and
that required source/promotion-boundary markers remain present.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, *needles: str) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            raise AssertionError(f"missing {needle!r} in {path}")


def main() -> None:
    residual53 = (3 + 3) * (3 ** 2) - 1
    extended71 = (3 + 3 + (3 - 1)) * (3 ** 2) - 1
    monster_from_c3 = 53 + 3 * 65610
    monster_from_ogg = 47 * 59 * 71

    assert residual53 == 53
    assert extended71 == 71
    assert monster_from_c3 == 196883
    assert monster_from_ogg == 196883
    assert 1 + monster_from_c3 == 196884
    assert 1 + residual53 == 54
    assert 6 + 4 == 10
    assert 8536 - 4223 == 4313
    assert 42 / 10 == 4.2
    assert 555245 - 554554 == 691
    assert 64 == 8 * 8
    assert 55517555010 / 1_000_000_000 == 55.51755501
    assert 55519414318 / 1_000_000_000 == 55.519414318

    require("DASHI/Moonshine/MonsterC3ResidualTernaryArithmeticExact.agda",
            "residual53FromTernaryNeighbour", "ogg71FromExtendedTernaryNeighbour",
            "arithmeticIdentityProvesMonsterModuleIntertwiner", "arithmeticIdentityProvesGravity")
    require("DASHI/Physics/Closure/MonsterC3ZetaEntropyGravityCrossPollinationExact.agda",
            "literalThreePhaseFibresUseOneCentralAction", "actualSingleProducerInhabited",
            "fixedRegularResidualSameActionSplitPaid", "zetaWeldCreatesQuantumGravity")
    require("DASHI/Physics/Chemistry/AmmoniaHamiltonianWavefunctionExact.agda",
            "10.1146/annurev.physchem.53.082201.124330", "10.1016/j.jms.2005.10.007",
            "10.1021/jp4016728", "literalOccupationBasisStatePaid",
            "numericRealSpaceWavefunctionCoefficientsPaid")
    require("DASHI/Physics/Chemistry/AmmoniaSTO3GFCIExact.agda",
            "10.1088/2058-9565/ad7d32", "555245", "sourceBackedFCIDiagonalizationPaid",
            "literalFCIEigenvectorCoefficientsImported")
    require("DASHI/Physics/Chemistry/AmmoniaSCIReleasedArtifactExact.agda",
            "07541705a0305e75dab1de5bc1b8324d66fee778", "55517555010", "55519414318",
            "paperBenchmarkAndArtifactAreSameNumericalObject", "matrixIndependentlyRediagonalizedByDASHI")
    require("DASHI/Physics/Chemistry/AmmoniaGroundStateC3ActionExact.agda",
            "groundDeterminantPhase", "closedShellDeterminantInvariantPaid", "realSpaceWavefunctionActionPaid")
    require("DASHI/Physics/Chemistry/AmmoniaMonster3BActionProbeExact.agda",
            "canonicalC3PhaseCoordinateIntertwiner", "trivialAnyGroupActionOnSingletonAvailable",
            "formalTrivialMonsterActionHasPhysicalContent", "monsterActionOnAmmoniaPaid")
    require("DASHI/Physics/Chemistry/AmmoniaH3PlusC3ResolvedReactionExact.agda",
            "fullProofRelevantC3ResolvedReactionTransitionPaid", "reactionExothermicityMagnitudeTenthsKJPerMol",
            "4313", "selectedC3EqualsFullProductPointGroup")
    require("DASHI/Physics/Chemistry/AmmoniaHydrogenAbstractionMechanismExact.agda",
            "10.1021/jp1001513", "10.1063/1.3605242", "sourceBackedAnalyticalPESPaid",
            "sourceBackedTimeDependentWavepacketDynamicsPaid", "uniqueMicroscopicTrajectoryDetermined")
    require("DASHI/Physics/Chemistry/AmmoniaHydrogenAbstraction369HyperfibreExact.agda",
            "literalChemistryHyperfibreInhabited", "atomicIdentityTransportPaid", "fibreCreatesMonsterAction")
    require("DASHI/Physics/Chemistry/AtomicPeriodicTable369C3EntropyIntertwinerExact.agda",
            "boundedGroundConfigurationElectronicC3ActionPaid", "literal369ReactionHyperformInstantiated",
            "fullRealSpaceElectronicC3ActionInstantiated", "universalElectronResolvedReactionEnergetics")
    require("DASHI/Physics/Closure/MonsterC3UniformCountingEnsembleExact.agda",
            "normalizedFiniteCountingWeightsPaid", "finCarrierIdentifiedWithLiteralMonsterStates",
            "uniformCountingMeasureIsPhysicalThermalEnsemble")
    require("DASHI/Physics/Closure/EntropyGravityIntertwinerBoundaryExact.agda",
            "scalarEntropyDensityDeterminesStressTensor", "entropyObservableAloneDerivesEinsteinDynamics",
            "jacobson1995LocalHorizonRoute", "padmanabhanNullEntropyDensityRoute")
    require("DASHI/Physics/Closure/Monster3Plus1PhysicalSymmetryTargetExact.agda",
            "monsterIsSymmetryOfObserved3Plus1Universe", "statusMeansUnpaidNotImpossible",
            "missingNovelQuantitativePrediction", "missingIndependentEmpiricalValidation")

    print("monster/C3/369 chemistry/entropy/gravity structural audit: ok")
    print("arithmetic: 53, 71, 196883, 196884, 54")
    print("NH3: published STO-3G benchmark and author-released CI artifacts remain separate")
    print("proton transfer: proof-relevant selected-C3 transport, PA difference 431.3 kJ/mol")
    print("author-released selected-CI artifact: exact 64x64 blob identity recorded; rediagonalization unpaid")


if __name__ == "__main__":
    main()
