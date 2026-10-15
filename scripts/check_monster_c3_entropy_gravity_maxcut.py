#!/usr/bin/env python3
"""Executable structural audit for the Monster/C3/chemistry/entropy/gravity max-cut.

This is deliberately not an Agda proof or physical validation. It checks exact
arithmetic and required fail-closed/source markers. Agda typechecking is separate.
"""

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
    assert 1 * 196883 == 196883
    assert 1 * 53 == 53
    assert 6 + 4 == 10
    assert 3 + 1 == 4
    assert 8 == 8
    assert 3 + 3 == 4 + 2
    assert 2 + 10 == 10 + 2
    assert 8536 / 10 == 853.6
    assert 42 / 10 == 4.2

    require(
        "DASHI/Moonshine/MonsterC3ResidualTernaryArithmeticExact.agda",
        "residual53FromTernaryNeighbour",
        "ogg71FromExtendedTernaryNeighbour",
        "arithmeticIdentityProvesMonsterModuleIntertwiner",
        "arithmeticIdentityProvesGravity",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3ZetaEntropyGravityCrossPollinationExact.agda",
        "literalThreePhaseFibresUseOneCentralAction",
        "actualSingleProducerInhabited",
        "fixedRegularResidualSameActionSplitPaid",
        "zetaWeldCreatesQuantumGravity",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaC3MolecularFixtureExact.agda",
        "C3v",
        "rotateHThreeTimes",
        "experimentalC3GeometryPaid",
        "ammoniaInversionIsProductsByproductsReaction",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaC3ElectronicSymmetryExact.agda",
        "10.1016/S0009-2614(02)00255-5",
        "10.1063/1.1711932",
        "(1a1)^2(2a1)^2(1e)^4(3a1)^2",
        "sourceBackedOrbitalSymmetryCoordinatesPaid",
        "fullAbInitioElectronicWavefunctionPaid",
        "sameObjectHamiltonianPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaProtonationReactionExact.agda",
        "10.1063/1.556018",
        "8536",
        "atomInventoryConservationPaid",
        "lewisElectronAndBondAccountingPaid",
        "sameReactionQuantitativeKineticsPaid",
        "protonAffinityDeterminesMicroscopicReactionPath",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaH3PlusProtonTransferExact.agda",
        "10.1016/0009-2614(74)89061-5",
        "H3+ + NH3 -> NH4+ + H2",
        "rateMantissaTenths",
        "42",
        "297",
        "20",
        "productsAndByproductsPaid",
        "sameReactionQuantitativeKineticsPaid",
        "numericLabTablePromotedToPrimaryPaperLocator",
        "microscopicTransitionPathPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AtomicPeriodicTable369C3EntropyIntertwinerExact.agda",
        "sourceBackedSameObjectC3GeometryFixturePaid",
        "sourceBackedElectronicIrrepCoordinatesPaid",
        "sourceBackedProtonationStoichiometryPaid",
        "sourceBackedProtonationThermochemistryPaid",
        "productsByproductsReactionFixturePaid",
        "sameReactionQuantitativeKineticsPaid",
        "fullC3ResolvedReactionTransportInstantiated",
        "microscopicTransitionPathPaid",
        "molecularEntropyImpliesPhysicalGravity",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3UniformCountingEnsembleExact.agda",
        "fineUniformNormalization",
        "coarseUniformNormalization",
        "normalizedFiniteCountingWeightsPaid",
        "finCarrierIdentifiedWithLiteralMonsterStates",
        "uniformCountingMeasureIsPhysicalThermalEnsemble",
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

    print("monster/C3/chemistry/entropy/gravity max-cut structural audit: ok")
    print(f"53 fixture: {residual53}")
    print(f"71 fixture: {extended71}")
    print(f"Monster degree via C3: {monster_degree_from_c3}")
    print(f"Monster degree via Ogg factors: {monster_degree_from_ogg}")
    print("NH3 electronic count: 6 A1 + 4 E = 10 electrons")
    print("NH3 + H+ protonation: H inventory 3+1=4; proton affinity 853.6 kJ/mol")
    print("H3+ + NH3: products NH4+ + H2; k=4.2e-9 at 297 K, +/-20% compilation row")
    print("uniform counting weights: 1/196883 and 1/53 normalize arithmetically")


if __name__ == "__main__":
    main()
