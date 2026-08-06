module DASHI.Physics.Foundations.Round5FullBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ParameterScaleTaxonomyExact as Parameter
import DASHI.Physics.Foundations.ParameterInformationGeometryExact as Information
import DASHI.Physics.Foundations.RGMDLExhaustionChambersExact as Flow
import DASHI.Physics.Foundations.DimensionPowerCountingBoundaryExact as Dimension
import DASHI.Physics.Foundations.AtomicFermionShellExact as Atomic
import DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact as AtomicBridge
import DASHI.Physics.Foundations.NuclearShellPairingExact as NuclearShell
import DASHI.Physics.Foundations.NuclearShapeInstabilityExact as NuclearShape
import DASHI.Physics.Foundations.CausalCodingCosmologyBoundaryExact as Coding
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as Geometry
import DASHI.Physics.Foundations.FiniteGraphGaugeScalarExact as FiniteGauge
import DASHI.Physics.Foundations.KernelQFTEmergenceObligations as Quantum
import DASHI.Physics.Foundations.UnifiedEffectiveActionBoundary as Unified
import DASHI.Physics.Foundations.Round5SourceAtlas as Sources
import DASHI.Papers.Unification.TheoremInterface as ExistingUnification

------------------------------------------------------------------------
-- Cumulative exact finite theorem surface.

record Round5FullBoundary : Set where
  field
    parameterScaleBoundary : Parameter.ParameterScaleBoundary
    parameterInformationBoundary : Information.ParameterInformationGeometryBoundary
    rgmdlExhaustionBoundary : Flow.RGMDLExhaustionBoundary
    dimensionSelectionBoundary : Dimension.DimensionSelectionBoundary
    atomicFermionBoundary : Atomic.AtomicFermionBoundary
    atomicValenceFermionBoundary : AtomicBridge.AtomicValenceFermionBoundary
    nuclearShellPairingBoundary : NuclearShell.NuclearShellPairingBoundary
    nuclearShapeBoundary : NuclearShape.NuclearShapeBoundary
    causalCodingCosmologyBoundary : Coding.CausalCodingCosmologyBoundary
    kernelGeometryBoundary : Geometry.KernelGeometryBoundary
    finiteGraphGaugeBoundary : FiniteGauge.FiniteGraphGaugeBoundary
    kernelQFTBoundary : Quantum.KernelQFTBoundary
    unifiedEffectiveActionBoundary : Unified.UnifiedEffectiveActionBoundary

    scaleOrbitCannotCollapse :
      Parameter.scaledObservable Parameter.unitScale
      ≡
      Parameter.scaledObservable Parameter.doubledScale
      →
      ⊥

    reparametrisedNormIsInvariant :
      Information.tangentNormSquare Information.lambdaChart
      ≡
      Information.tangentNormSquare Information.etaChart

    canonicalParameterViable :
      Flow.fullyViable Flow.viableParameter ≡ true

    yangMillsMarginalInFour :
      Dimension.yangMillsClass Dimension.dimension4
      ≡
      Dimension.marginalClass

    thirdAtomicShellHasCapacityEighteen :
      Atomic.shellCapacity 3 ≡ 18

    fermionSwapTwiceReturnsState :
      AtomicBridge.swapFermions
        (AtomicBridge.swapFermions AtomicBridge.canonicalAntisymmetricPair)
      ≡
      AtomicBridge.canonicalAntisymmetricPair

    protonClosureIsMagic :
      NuclearShell.closureStatus NuclearShell.canonicalProtonClosure
      ≡
      NuclearShell.magicClosure

    fixedDensityFermiTermIsExtensive :
      NuclearShape.bulkFermiEnergy 8
      ≡
      NuclearShape.bulkFermiEnergy 4
      +
      NuclearShape.bulkFermiEnergy 4

    cmbProjectionIsManyToOne :
      Coding.observeCMB Coding.earlyStateA
      ≡
      Coding.observeCMB Coding.earlyStateB

    equalDensityDoesNotFixStressProfile :
      Geometry.energyDensity Geometry.stressProfileA
      ≡
      Geometry.energyDensity Geometry.stressProfileB

    finiteGaugeLoopIsInvariant :
      FiniteGauge.loopHolonomy FiniteGauge.transformedConnection
      ≡
      FiniteGauge.loopHolonomy FiniteGauge.canonicalConnection

    graphLoopHasTwistHolonomy :
      Quantum.triangleHolonomy ≡ Quantum.gaugeTwist

    terminalUnificationRemainsFalse :
      ExistingUnification.terminalUnificationPromoted
        ExistingUnification.canonicalUnificationPaperTheoremInterface
      ≡
      false

    sourceCountIsFourteen :
      Sources.canonicalRound5SourceCount ≡ 14

open Round5FullBoundary public

canonicalRound5FullBoundary : Round5FullBoundary
canonicalRound5FullBoundary =
  record
    { parameterScaleBoundary =
        Parameter.canonicalParameterScaleBoundary
    ; parameterInformationBoundary =
        Information.canonicalParameterInformationGeometryBoundary
    ; rgmdlExhaustionBoundary =
        Flow.canonicalRGMDLExhaustionBoundary
    ; dimensionSelectionBoundary =
        Dimension.canonicalDimensionSelectionBoundary
    ; atomicFermionBoundary =
        Atomic.canonicalAtomicFermionBoundary
    ; atomicValenceFermionBoundary =
        AtomicBridge.canonicalAtomicValenceFermionBoundary
    ; nuclearShellPairingBoundary =
        NuclearShell.canonicalNuclearShellPairingBoundary
    ; nuclearShapeBoundary =
        NuclearShape.canonicalNuclearShapeBoundary
    ; causalCodingCosmologyBoundary =
        Coding.canonicalCausalCodingCosmologyBoundary
    ; kernelGeometryBoundary =
        Geometry.canonicalKernelGeometryBoundary
    ; finiteGraphGaugeBoundary =
        FiniteGauge.canonicalFiniteGraphGaugeBoundary
    ; kernelQFTBoundary =
        Quantum.canonicalKernelQFTBoundary
    ; unifiedEffectiveActionBoundary =
        Unified.canonicalUnifiedEffectiveActionBoundary
    ; scaleOrbitCannotCollapse =
        Parameter.unitAndDoubledScaleAreDistinct
    ; reparametrisedNormIsInvariant =
        refl
    ; canonicalParameterViable =
        refl
    ; yangMillsMarginalInFour =
        refl
    ; thirdAtomicShellHasCapacityEighteen =
        refl
    ; fermionSwapTwiceReturnsState =
        refl
    ; protonClosureIsMagic =
        refl
    ; fixedDensityFermiTermIsExtensive =
        refl
    ; cmbProjectionIsManyToOne =
        refl
    ; equalDensityDoesNotFixStressProfile =
        refl
    ; finiteGaugeLoopIsInvariant =
        refl
    ; graphLoopHasTwistHolonomy =
        refl
    ; terminalUnificationRemainsFalse =
        ExistingUnification.unificationPaperInterfaceTerminalFalse
    ; sourceCountIsFourteen =
        refl
    }
