{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayCompleteDensityTransferMixingBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.Balaban1989BetaHistoryToCanonicalCompleteDensityExact as Canonical
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact as Region
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG
import DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerExact as DenseMarked

------------------------------------------------------------------------
-- Exact boundary between the tightened Bałaban complete-density lane and the
-- literal transfer/mixing F1 normal form.
--
-- What is already constructive/compiler-owned in the repository:
--
--   beta history
--     -> same couplingAt in the CMP122 effective-density flow
--     -> same runningCoupling coordinate in the canonical YM4 state
--     -> source Section-2 bounds assemble the rational invariant region.
--
-- Earlier bookkeeping made the next bridge look artificially unique:
--
--   complete density -> full adjacent-slice RN defect in L-infinity -> F1.
--
-- That route remains valid if a source theorem pays it, but it is no longer a
-- primitive requirement.  `YMClayDenseL2CorrelationBidiParityExact` and
-- `YMClayDenseMarkedSourceF1ProducerExact` expose the weaker source-native lane:
--
--   same beta-driven density
--     -> selected marked/local Wilson observables
--     -> published mixed-source separation decay
--     -> same-object envelope = c_k ||psi||_2^2 normalization on dense L2_0
--     -> full physical L2_0 decorrelator.
--
-- Therefore the exact remaining complete-density/source bridge can be paid by
-- either (A) the stronger full density defect or (B) the dense marked-source
-- application/normalization weld.  Neither is manufactured from the Section-2
-- invariant-region fields alone.
------------------------------------------------------------------------

data CompleteDensityTransferMixingBoundaryPresent : Set where
  completeDensityTransferMixingBoundaryPresent :
    CompleteDensityTransferMixingBoundaryPresent

betaDrivenFlowOwner : String
betaDrivenFlowOwner =
  "Balaban1989BetaDrivenCompleteDensityFlowExact"

canonicalDensityOwner : String
canonicalDensityOwner =
  "Balaban1989BetaHistoryToCanonicalCompleteDensityExact"

regionDictionaryOwner : String
regionDictionaryOwner =
  "Balaban1989CompleteDensityToYM4RegionExact"

physicalGapRegionOwner : String
physicalGapRegionOwner =
  "BalabanYM4RGInvariantRegionPhysicalGapExact"

denseMarkedF1Owner : String
denseMarkedF1Owner =
  "YMClayDenseMarkedSourceF1ProducerExact"

betaAndCompleteDensityUseSameCouplingHistory : Bool
betaAndCompleteDensityUseSameCouplingHistory = true

betaAndCompleteDensityUseSameCouplingHistoryIsTrue :
  betaAndCompleteDensityUseSameCouplingHistory ≡ true
betaAndCompleteDensityUseSameCouplingHistoryIsTrue = refl

section2BoundsAssembleYM4InvariantRegion : Bool
section2BoundsAssembleYM4InvariantRegion = true

section2BoundsAssembleYM4InvariantRegionIsTrue :
  section2BoundsAssembleYM4InvariantRegion ≡ true
section2BoundsAssembleYM4InvariantRegionIsTrue = refl

section2BoundsDirectlyPayJointSliceDensityDefect : Bool
section2BoundsDirectlyPayJointSliceDensityDefect = false

section2BoundsDirectlyPayJointSliceDensityDefectIsFalse :
  section2BoundsDirectlyPayJointSliceDensityDefect ≡ false
section2BoundsDirectlyPayJointSliceDensityDefectIsFalse = refl

conditionalCovarianceCapDirectlyPaysFullL2Decorrelator : Bool
conditionalCovarianceCapDirectlyPaysFullL2Decorrelator = false

conditionalCovarianceCapDirectlyPaysFullL2DecorrelatorIsFalse :
  conditionalCovarianceCapDirectlyPaysFullL2Decorrelator ≡ false
conditionalCovarianceCapDirectlyPaysFullL2DecorrelatorIsFalse = refl

fullJointDensityLinfinityDefectPrimitiveForF1 : Bool
fullJointDensityLinfinityDefectPrimitiveForF1 = false

fullJointDensityLinfinityDefectPrimitiveForF1IsFalse :
  fullJointDensityLinfinityDefectPrimitiveForF1 ≡ false
fullJointDensityLinfinityDefectPrimitiveForF1IsFalse = refl

denseMarkedSourceAlternativeRecorded : Bool
denseMarkedSourceAlternativeRecorded = true

denseMarkedSourceAlternativeRecordedIsTrue :
  denseMarkedSourceAlternativeRecorded ≡ true
denseMarkedSourceAlternativeRecordedIsTrue = refl

completeDensityInvariantRegionConstructsPositivePhysicalMassFloor : Bool
completeDensityInvariantRegionConstructsPositivePhysicalMassFloor = false

completeDensityInvariantRegionConstructsPositivePhysicalMassFloorIsFalse :
  completeDensityInvariantRegionConstructsPositivePhysicalMassFloor ≡ false
completeDensityInvariantRegionConstructsPositivePhysicalMassFloorIsFalse = refl

record CompleteDensityToLiteralTwoSliceMixingTarget : Set₁ where
  field
    Cutoff : Set
    DensityState : Cutoff → Set
    SlicePairLaw : Cutoff → Set
    ProductMarginalLaw : Cutoff → Set
    Defect : Cutoff → Set

    densityState : (cutoff : Cutoff) → DensityState cutoff
    slicePairLaw : (cutoff : Cutoff) → SlicePairLaw cutoff
    productMarginalLaw : (cutoff : Cutoff) → ProductMarginalLaw cutoff
    defect : (cutoff : Cutoff) → Defect cutoff

    SamePhysicalCompleteDensityState : Set
    samePhysicalCompleteDensityState : SamePhysicalCompleteDensityState

    LiteralAdjacentSliceLawIdentified : Set
    literalAdjacentSliceLawIdentified : LiteralAdjacentSliceLawIdentified

    ProductMarginalsIdentified : Set
    productMarginalsIdentified : ProductMarginalsIdentified

    UniformDensityDefectBound : Set
    uniformDensityDefectBound : UniformDensityDefectBound

open CompleteDensityToLiteralTwoSliceMixingTarget public

record CompleteDensityToDenseMarkedF1Target : Set₁ where
  field
    SameBetaDrivenDensityAndMarkedSourceState : Set
    sameBetaDrivenDensityAndMarkedSourceState :
      SameBetaDrivenDensityAndMarkedSourceState

    LiteralWilsonDenseCylinderAlgebraIdentified : Set
    literalWilsonDenseCylinderAlgebraIdentified :
      LiteralWilsonDenseCylinderAlgebraIdentified

    SelectedMarkedDirectionsArePhysicalSliceObservables : Set
    selectedMarkedDirectionsArePhysicalSliceObservables :
      SelectedMarkedDirectionsArePhysicalSliceObservables

    SourceEnvelopeUsesPhysicalL2Normalization : Set
    sourceEnvelopeUsesPhysicalL2Normalization :
      SourceEnvelopeUsesPhysicalL2Normalization

open CompleteDensityToDenseMarkedF1Target public

-- The following two are source-written composition/bookkeeping claims on this
-- branch.  No exact-head Agda kernel receipt was run in this connector tranche.
sameTrajectoryCompilerLevel : ProofLevel
sameTrajectoryCompilerLevel = conditional

completeDensityRegionAssemblyLevel : ProofLevel
completeDensityRegionAssemblyLevel = conditional

completeDensityToLiteralMixingBridgeLevel : ProofLevel
completeDensityToLiteralMixingBridgeLevel = conditional

completeDensityToDenseMarkedF1BridgeLevel : ProofLevel
completeDensityToDenseMarkedF1BridgeLevel = conditional

-- This is the generic dense marked-source compiler level, imported rather than
-- re-declared as a second theorem family.
denseMarkedSourceF1CompilerLevel : ProofLevel
denseMarkedSourceF1CompilerLevel = DenseMarked.denseMarkedSourceF1CompilerLevel

physicalMassFloorFromCompleteDensityLevel : ProofLevel
physicalMassFloorFromCompleteDensityLevel = conditional
