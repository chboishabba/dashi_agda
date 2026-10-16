#!/usr/bin/env python3
"""Structural audit for the Monster/C3/369 chemistry/entropy/gravity max-cut.

This is not an Agda typecheck and not physical validation. It checks exact
finite arithmetic plus the presence of terminal proof/promotion markers.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, *needles: str) -> None:
    """Require every marker string to occur in one repository file."""
    text = (ROOT / path).read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            raise AssertionError(f"missing {needle!r} in {path}")


def check(name: str, condition: bool) -> None:
    """Raise explicitly when a finite arithmetic regression fails, even under -O."""
    if not condition:
        raise AssertionError(f"failed arithmetic check: {name}")


def main() -> None:
    """Run finite arithmetic and structural-marker regression checks."""
    check("ternary residual 53", (3 + 3) * 9 - 1 == 53)
    check("extended ternary 71", (3 + 3 + 2) * 9 - 1 == 71)
    check("Monster degree two ways", 53 + 3 * 65610 == 196883 == 47 * 59 * 71)
    check("zeta model dimension", 729 * 90 == 65610)
    check("three regular fibres", 3 * 65610 == 196830)
    check("regular plus residual", 196830 + 53 == 196883)

    check("proton-affinity difference", 8536 - 4223 == 4313)
    check("published STO-3G FCI-HF gap", 555245 - 554554 == 691)
    check("released SCI energy encoding", 55517555010 / 1_000_000_000 == 55.51755501)
    check("released FCI-run energy encoding", 55519414318 / 1_000_000_000 == 55.519414318)
    check("native-zeta normalization numerator", 1 * 65610 == 65610)

    require(
        "DASHI/Physics/Chemistry/AmmoniaC3RegularRepresentationExact.agda",
        "ammoniaA1PlusEGeneratorCancels",
        "monsterRegularBlockMultiplicity",
        "monsterResidualMultiplicity",
        "sameRegularC3MotifCreatesMonsterModule",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BC3QuotientLiftExact.agda",
        "nh3MonsterRoundTrip",
        "monsterNH3RoundTrip",
        "nh3MonsterMultiplicationIntertwines",
        "nh3MonsterInversionIntertwines",
        "nh3MonsterFourierRowsIntertwine",
        "quotientIntertwinerCreatesStateIntertwiner",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BPhaseQuotientNonFactorabilityExact.agda",
        "phaseCannotRecoverModelBasis",
        "phaseCannotRecoverWeightPosition",
        "phaseCannotRecoverMultiplicityCoordinate",
    )
    require(
        "DASHI/Physics/Chemistry/Atomic369Kernel6HeisenbergBridgeExact.agda",
        "kernel6RoundTrip",
        "x6RoundTrip",
        "physicalNH3StateToKernel6AssignmentPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BRefinedStateLiftCompilerExact.agda",
        "refinedModelRoundTrip",
        "modelRefinedRoundTrip",
        "actualRecognitionLiftCompilerPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BNative369FineCarrierExact.agda",
        "native369RoundTrip",
        "model369RoundTrip",
        "native369ActualRoundTrip",
        "actualNative369RoundTrip",
        "physicalNH3StateToNative369FineCoordinatePaid",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3Native369ConsumerSufficiencyExact.agda",
        "phaseObserverSufficientForPhase",
        "phaseObserverNotSufficientForWeight",
        "phaseObserverNotSufficientForMultiplicity",
        "phaseObserverNotSufficientForFineState",
        "native369ObserverSufficientForFineState",
        "phaseFineStateDoesNotFactor",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3Native369ZetaCountingEnsembleExact.agda",
        "zetaStateCount",
        "65610",
        "native369ZetaCountingEnsemble",
        "nativeUniformCountingIsPhysicalThermalEnsemble",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaHamiltonianWavefunctionExact.agda",
        "sameObjectSymbolicHamiltonianExpressionPaid",
        "energyValuedHamiltonianOperatorPaid",
        "literalOccupationBasisStatePaid",
        "numericRealSpaceWavefunctionCoefficientsPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaGroundStateC3ActionExact.agda",
        "foldOccupiedPhase",
        "determinantPhaseComputedFromOccupiedCarrier",
        "trivialGroundConfigurationC3RepresentationPaid",
        "nontrivialRealSpaceWavefunctionC3ActionPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaHydrogenAbstraction369HyperfibreExact.agda",
        "atomic369InventoryEndpointsPaid",
        "individualAtomIdentityTransportPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaSTO3GFCIExact.agda",
        "10.1088/2058-9565/ad7d32",
        "sourceBackedFCIDiagonalizationPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaSCIReleasedArtifactExact.agda",
        "07541705a0305e75dab1de5bc1b8324d66fee778",
        "55517555010",
        "55519414318",
        "paperBenchmarkAndArtifactAreSameNumericalObject",
        "matrixIndependentlyRediagonalizedByDASHI",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaH3PlusC3ResolvedReactionExact.agda",
        "fullProofRelevantC3ResolvedReactionTransitionPaid",
        "4313",
        "selectedC3EqualsFullProductPointGroup",
    )
    require(
        "DASHI/Reasoning/Trialectic369Selected3BSemanticProjectedCompletionExact.agda",
        "onlyLinearRetractionAndProjectedActionRemain",
        "actualLinearRetractionInhabitedHere",
        "projectedActionInputInhabitedHere",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3EntropyGravityMaxCutExact.agda",
        "fullMonsterZetaNative369FineCarrierPaid",
        "actualZetaRecognitionNative369CompilerPaid",
        "physicalNH3Native369FineCoordinatePaid",
        "native369ZetaCountingEnsemblePaid",
        "observed3Plus1MonsterPaid",
    )
    require(
        "DASHI/Physics/Closure/EntropyGravityIntertwinerBoundaryExact.agda",
        "scalarEntropyDensityDeterminesStressTensor",
        "entropyObservableAloneDerivesEinsteinDynamics",
    )

    print("monster/C3/369 chemistry/entropy/gravity structural audit: ok")
    print("NH3 A1+E = one regular-C3 block; Monster bulk uses 65610 blocks + residual 53")
    print("phase quotient: exact for phase consumers, non-sufficient for fine-state consumers")
    print("Monster zeta model: native369 Kernel6 x (Completed10 x T^2), 65610 microstates")
    print("physical NH3->native369 state assignment remains explicitly unpaid")
    print("hydrogen-abstraction 369 endpoint inventory is paid; individual atom identity is not")
    print("symbolic Hamiltonian expression is paid; evaluated energy operator is not")
    print("published benchmark and author-released CI artifacts remain distinct")
    print("independent matrix rediagonalization remains explicitly unpaid")


if __name__ == "__main__":
    main()
