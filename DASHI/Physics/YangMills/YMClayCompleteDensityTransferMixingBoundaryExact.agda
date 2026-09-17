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

------------------------------------------------------------------------
-- Exact boundary between the newly tightened Bałaban complete-density lane and
-- the literal transfer/mixing F1 normal form.
--
-- What is already constructive/compiler-owned in the repository:
--
--   beta history
--     -> same couplingAt in the CMP122 effective-density flow
--     -> same runningCoupling coordinate in the canonical YM4 state
--     -> source Section-2 bounds assemble the rational invariant region.
--
-- What does NOT follow from those interfaces as currently typed:
--
--   conditionalCovarianceNorm <= covarianceCap
--     -> full adjacent-slice joint-density defect
--     -> uniform decorrelator for every vacuum-orthogonal L2 state
--
-- nor:
--
--   InYM4RGInvariantRegion
--     -> InYM4RGPhysicalGapRegion.
--
-- The latter record explicitly adds a positive massFloor and the inequality
-- massFloor <= latticeDecayExponent * inversePhysicalSpacing.
--
-- This owner is proof-search bookkeeping.  It does not assert that no such
-- theorem can be proved from stronger source content; it records that the
-- currently owned interfaces do not contain that implication.
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

completeDensityInvariantRegionConstructsPositivePhysicalMassFloor : Bool
completeDensityInvariantRegionConstructsPositivePhysicalMassFloor = false

completeDensityInvariantRegionConstructsPositivePhysicalMassFloorIsFalse :
  completeDensityInvariantRegionConstructsPositivePhysicalMassFloor ≡ false
completeDensityInvariantRegionConstructsPositivePhysicalMassFloorIsFalse = refl

-- The strongest currently useful next theorem shape.  A future source/repo
-- bridge may pay either this density form directly or an equivalent operator
-- bound, but no such witness is manufactured here.
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

sameTrajectoryCompilerLevel : ProofLevel
sameTrajectoryCompilerLevel = machineChecked

completeDensityRegionAssemblyLevel : ProofLevel
completeDensityRegionAssemblyLevel = machineChecked

completeDensityToLiteralMixingBridgeLevel : ProofLevel
completeDensityToLiteralMixingBridgeLevel = conditional

physicalMassFloorFromCompleteDensityLevel : ProofLevel
physicalMassFloorFromCompleteDensityLevel = conditional
