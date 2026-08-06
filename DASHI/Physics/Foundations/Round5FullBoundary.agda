module DASHI.Physics.Foundations.Round5FullBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ParameterScaleTaxonomyExact as Parameter
import DASHI.Physics.Foundations.ParameterInformationGeometryExact as Information
import DASHI.Physics.Foundations.ScaleInvariantTheorySelectionExact as ScaleTheory
import DASHI.Physics.Foundations.RGMDLExhaustionChambersExact as Flow
import DASHI.Physics.Foundations.DimensionPowerCountingBoundaryExact as Dimension
import DASHI.Physics.Foundations.DiscreteLorentzEmergenceBoundaryExact as Lorentz
import DASHI.Physics.Foundations.AtomicFermionShellExact as Atomic
import DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact as AtomicBridge
import DASHI.Physics.Foundations.AtomicGenerationPipelineExact as AtomicPipeline
import DASHI.Physics.Foundations.NuclearShellPairingExact as NuclearShell
import DASHI.Physics.Foundations.NuclearShapeInstabilityExact as NuclearShape
import DASHI.Physics.Foundations.NuclearResponseComplexityExact as NuclearResponse
import DASHI.Physics.Foundations.CausalCodingCosmologyBoundaryExact as Coding
import DASHI.Physics.Foundations.CMBInformationChannelExact as CMBChannel
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as Geometry
import DASHI.Physics.Foundations.FiniteStressConservationGeodesicExact as FiniteGeometry
import DASHI.Physics.Foundations.FiniteGraphGaugeScalarExact as FiniteGauge
import DASHI.Physics.Foundations.FiniteFockExcitationExact as Fock
import DASHI.Physics.Foundations.KernelQFTEmergenceObligations as Quantum
import DASHI.Physics.Foundations.KernelEmergenceHypothesesExact as Hypotheses
import DASHI.Physics.Foundations.UnifiedEffectiveActionBoundary as Unified
import DASHI.Physics.Foundations.Round5SourceAtlas as Sources
import DASHI.Papers.Unification.TheoremInterface as ExistingUnification

------------------------------------------------------------------------
-- Cumulative exact finite theorem surface.

record Round5FullBoundary : Set where
  field
    parameterScaleBoundary : Parameter.ParameterScaleBoundary
    parameterInformationBoundary : Information.ParameterInformationGeometryBoundary
    scaleTheoryBoundary : ScaleTheory.ScaleInvariantTheorySelectionBoundary
    rgmdlExhaustionBoundary : Flow.RGMDLExhaustionBoundary
    dimensionSelectionBoundary : Dimension.DimensionSelectionBoundary
    discreteLorentzBoundary : Lorentz.DiscreteLorentzBoundary
    atomicFermionBoundary : Atomic.AtomicFermionBoundary
    atomicValenceFermionBoundary : AtomicBridge.AtomicValenceFermionBoundary
    atomicGenerationBoundary : AtomicPipeline.AtomicGenerationBoundary
    nuclearShellPairingBoundary : NuclearShell.NuclearShellPairingBoundary
    nuclearShapeBoundary : NuclearShape.NuclearShapeBoundary
    nuclearResponseBoundary : NuclearResponse.NuclearResponseComplexityBoundary
    causalCodingCosmologyBoundary : Coding.CausalCodingCosmologyBoundary
    cmbInformationBoundary : CMBChannel.CMBInformationChannelBoundary
    kernelGeometryBoundary : Geometry.KernelGeometryBoundary
    finiteStressGeometryBoundary : FiniteGeometry.FiniteStressGeodesicBoundary
    finiteGraphGaugeBoundary : FiniteGauge.FiniteGraphGaugeBoundary
    finiteFockBoundary : Fock.FiniteFockExcitationBoundary
    kernelQFTBoundary : Quantum.KernelQFTBoundary
    kernelEmergenceHypothesisBoundary :
      Hypotheses.KernelEmergenceHypothesisBoundary
    unifiedEffectiveActionBoundary : Unified.UnifiedEffectiveActionBoundary

    scaleOrbitCannotCollapse :
      Parameter.scaledObservable Parameter.unitScale
      ≡
      Parameter.scaledObservable Parameter.doubledScale
      →
      ⊥

    buckinghamWitnessCloses :
      ScaleTheory.sameDimension
        (ScaleTheory.multiplyDimension
          ScaleTheory.speedQuantityDimension
          ScaleTheory.timeQuantityDimension)
        ScaleTheory.lengthQuantityDimension

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

    infraredDispersionResidualVanishes :
      Lorentz.relativisticResidual Lorentz.canonicalInfraredDispersion ≡ 0

    thirdAtomicShellHasCapacityEighteen :
      Atomic.shellCapacity 3 ≡ 18

    fermionSwapTwiceReturnsState :
      AtomicBridge.swapFermions
        (AtomicBridge.swapFermions AtomicBridge.canonicalAntisymmetricPair)
      ≡
      AtomicBridge.canonicalAntisymmetricPair

    atomicPipelineChargeIsEighteen :
      Atomic.protonNumber
        (AtomicPipeline.species AtomicPipeline.canonicalFiniteAtomPipeline)
      ≡
      18

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

    largeGapSuppressesFiniteResponse :
      NuclearResponse.responseBound NuclearResponse.gapFour
      ≤
      NuclearResponse.responseBound NuclearResponse.gapOne

    cmbProjectionIsManyToOne :
      Coding.observeCMB Coding.earlyStateA
      ≡
      Coding.observeCMB Coding.earlyStateB

    cmbChannelErasesABDistinguishability :
      CMBChannel.reducedDistinguishability
        (CMBChannel.cmbChannel CMBChannel.earlyDensityA)
        (CMBChannel.cmbChannel CMBChannel.earlyDensityB)
      ≡
      0

    equalDensityDoesNotFixStressProfile :
      Geometry.energyDensity Geometry.stressProfileA
      ≡
      Geometry.energyDensity Geometry.stressProfileB

    cycleCurrentIsConserved :
      FiniteGeometry.vertex0Divergence FiniteGeometry.canonicalCycleCurrent
      ≡
      FiniteGeometry.divergenceZero

    finiteGaugeLoopIsInvariant :
      FiniteGauge.loopHolonomy FiniteGauge.transformedConnection
      ≡
      FiniteGauge.loopHolonomy FiniteGauge.canonicalConnection

    canonicalFockDatumIsOnMassShell :
      Fock.onMassShell Fock.canonicalMassShellDatum

    graphLoopHasTwistHolonomy :
      Quantum.triangleHolonomy ≡ Quantum.gaugeTwist

    macroscopicQFTCorrectionVanishes :
      Hypotheses.qftIrrelevantCorrection Hypotheses.macroscopicScale ≡ 0

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
    ; scaleTheoryBoundary =
        ScaleTheory.canonicalScaleInvariantTheorySelectionBoundary
    ; rgmdlExhaustionBoundary =
        Flow.canonicalRGMDLExhaustionBoundary
    ; dimensionSelectionBoundary =
        Dimension.canonicalDimensionSelectionBoundary
    ; discreteLorentzBoundary =
        Lorentz.canonicalDiscreteLorentzBoundary
    ; atomicFermionBoundary =
        Atomic.canonicalAtomicFermionBoundary
    ; atomicValenceFermionBoundary =
        AtomicBridge.canonicalAtomicValenceFermionBoundary
    ; atomicGenerationBoundary =
        AtomicPipeline.canonicalAtomicGenerationBoundary
    ; nuclearShellPairingBoundary =
        NuclearShell.canonicalNuclearShellPairingBoundary
    ; nuclearShapeBoundary =
        NuclearShape.canonicalNuclearShapeBoundary
    ; nuclearResponseBoundary =
        NuclearResponse.canonicalNuclearResponseComplexityBoundary
    ; causalCodingCosmologyBoundary =
        Coding.canonicalCausalCodingCosmologyBoundary
    ; cmbInformationBoundary =
        CMBChannel.canonicalCMBInformationChannelBoundary
    ; kernelGeometryBoundary =
        Geometry.canonicalKernelGeometryBoundary
    ; finiteStressGeometryBoundary =
        FiniteGeometry.canonicalFiniteStressGeodesicBoundary
    ; finiteGraphGaugeBoundary =
        FiniteGauge.canonicalFiniteGraphGaugeBoundary
    ; finiteFockBoundary =
        Fock.canonicalFiniteFockExcitationBoundary
    ; kernelQFTBoundary =
        Quantum.canonicalKernelQFTBoundary
    ; kernelEmergenceHypothesisBoundary =
        Hypotheses.canonicalKernelEmergenceHypothesisBoundary
    ; unifiedEffectiveActionBoundary =
        Unified.canonicalUnifiedEffectiveActionBoundary
    ; scaleOrbitCannotCollapse =
        Parameter.unitAndDoubledScaleAreDistinct
    ; buckinghamWitnessCloses =
        refl
    ; reparametrisedNormIsInvariant =
        refl
    ; canonicalParameterViable =
        refl
    ; yangMillsMarginalInFour =
        refl
    ; infraredDispersionResidualVanishes =
        refl
    ; thirdAtomicShellHasCapacityEighteen =
        refl
    ; fermionSwapTwiceReturnsState =
        refl
    ; atomicPipelineChargeIsEighteen =
        refl
    ; protonClosureIsMagic =
        refl
    ; fixedDensityFermiTermIsExtensive =
        refl
    ; largeGapSuppressesFiniteResponse =
        NuclearResponse.largeGapHasSmallerResponseBound
    ; cmbProjectionIsManyToOne =
        refl
    ; cmbChannelErasesABDistinguishability =
        refl
    ; equalDensityDoesNotFixStressProfile =
        refl
    ; cycleCurrentIsConserved =
        refl
    ; finiteGaugeLoopIsInvariant =
        refl
    ; canonicalFockDatumIsOnMassShell =
        refl
    ; graphLoopHasTwistHolonomy =
        refl
    ; macroscopicQFTCorrectionVanishes =
        refl
    ; terminalUnificationRemainsFalse =
        ExistingUnification.unificationPaperInterfaceTerminalFalse
    ; sourceCountIsFourteen =
        refl
    }
