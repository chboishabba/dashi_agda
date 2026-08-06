module DASHI.Physics.Foundations.Round5FullBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ParameterScaleTaxonomyExact as Parameter
import DASHI.Physics.Foundations.RGMDLExhaustionChambersExact as Flow
import DASHI.Physics.Foundations.DimensionPowerCountingBoundaryExact as Dimension
import DASHI.Physics.Foundations.AtomicFermionShellExact as Atomic
import DASHI.Physics.Foundations.NuclearShellPairingExact as NuclearShell
import DASHI.Physics.Foundations.NuclearShapeInstabilityExact as NuclearShape
import DASHI.Physics.Foundations.CausalCodingCosmologyBoundaryExact as Coding
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as Geometry
import DASHI.Physics.Foundations.KernelQFTEmergenceObligations as Quantum
import DASHI.Physics.Foundations.UnifiedEffectiveActionBoundary as Unified
import DASHI.Physics.Foundations.Round5SourceAtlas as Sources

------------------------------------------------------------------------
-- Cumulative exact finite theorem surface.

record Round5FullBoundary : Set where
  field
    parameterScaleBoundary : Parameter.ParameterScaleBoundary
    rgmdlExhaustionBoundary : Flow.RGMDLExhaustionBoundary
    dimensionSelectionBoundary : Dimension.DimensionSelectionBoundary
    atomicFermionBoundary : Atomic.AtomicFermionBoundary
    nuclearShellPairingBoundary : NuclearShell.NuclearShellPairingBoundary
    nuclearShapeBoundary : NuclearShape.NuclearShapeBoundary
    causalCodingCosmologyBoundary : Coding.CausalCodingCosmologyBoundary
    kernelGeometryBoundary : Geometry.KernelGeometryBoundary
    kernelQFTBoundary : Quantum.KernelQFTBoundary
    unifiedEffectiveActionBoundary : Unified.UnifiedEffectiveActionBoundary

    scaleOrbitCannotCollapse :
      Parameter.scaledObservable Parameter.unitScale
      ≡
      Parameter.scaledObservable Parameter.doubledScale
      →
      ⊥

    canonicalParameterViable :
      Flow.fullyViable Flow.viableParameter ≡ true

    yangMillsMarginalInFour :
      Dimension.yangMillsClass Dimension.dimension4
      ≡
      Dimension.marginalClass

    thirdAtomicShellHasCapacityEighteen :
      Atomic.shellCapacity 3 ≡ 18

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

    graphLoopHasTwistHolonomy :
      Quantum.triangleHolonomy ≡ Quantum.gaugeTwist

    terminalUnificationRemainsFalse :
      Unified.ExistingUnification.terminalUnificationPromoted
        Unified.ExistingUnification.canonicalUnificationPaperTheoremInterface
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
    ; rgmdlExhaustionBoundary =
        Flow.canonicalRGMDLExhaustionBoundary
    ; dimensionSelectionBoundary =
        Dimension.canonicalDimensionSelectionBoundary
    ; atomicFermionBoundary =
        Atomic.canonicalAtomicFermionBoundary
    ; nuclearShellPairingBoundary =
        NuclearShell.canonicalNuclearShellPairingBoundary
    ; nuclearShapeBoundary =
        NuclearShape.canonicalNuclearShapeBoundary
    ; causalCodingCosmologyBoundary =
        Coding.canonicalCausalCodingCosmologyBoundary
    ; kernelGeometryBoundary =
        Geometry.canonicalKernelGeometryBoundary
    ; kernelQFTBoundary =
        Quantum.canonicalKernelQFTBoundary
    ; unifiedEffectiveActionBoundary =
        Unified.canonicalUnifiedEffectiveActionBoundary
    ; scaleOrbitCannotCollapse =
        Parameter.unitAndDoubledScaleAreDistinct
    ; canonicalParameterViable =
        refl
    ; yangMillsMarginalInFour =
        refl
    ; thirdAtomicShellHasCapacityEighteen =
        refl
    ; protonClosureIsMagic =
        refl
    ; fixedDensityFermiTermIsExtensive =
        refl
    ; cmbProjectionIsManyToOne =
        refl
    ; equalDensityDoesNotFixStressProfile =
        refl
    ; graphLoopHasTwistHolonomy =
        refl
    ; terminalUnificationRemainsFalse =
        Unified.existingUnificationTerminalStillFalse
    ; sourceCountIsFourteen =
        refl
    }
