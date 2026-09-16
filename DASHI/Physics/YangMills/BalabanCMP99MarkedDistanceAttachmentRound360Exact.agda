{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP99MarkedDistanceAttachmentRound360Exact where

------------------------------------------------------------------------
-- ROUND360 / CMP99 MARKED BRANCH = SOURCE GEOMETRY + SAME-OBJECT ATTACHMENT
--
-- R357 needs the unweighted marked branch
--
--   collarRadius <= markedDistance.
--
-- The mature marked-walk owner says the surviving CMP99 term is controlled by
-- distance from the walk footprint to the domain discrepancy, but that source
-- discrepancy metric is not definitionally the selected R355/R357
-- `markedDistance` coordinate.
--
-- Therefore the least-privilege source-facing split is:
--
--   G_CMP99     : collarRadius <= cmp99DiscrepancyDistance
--   G_markAttach: selectedMarkedDistance = cmp99DiscrepancyDistance.
--
-- Equality transport then constructs the exact marked branch consumed by R357.
-- This module does not manufacture CMP99 geometry or identify metrics by name.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP99MarkedDistanceAttachment : Set₁ where
  field
    collarRadius : ℝ
    cmp99DiscrepancyDistance : ℝ
    selectedMarkedDistance : ℝ

    -- Source geometry from the literal surviving-walk/domain-discrepancy
    -- comparison on the selected near collar.
    sourceCollarBelowCMP99Discrepancy :
      collarRadius ≤ℝ cmp99DiscrepancyDistance

    -- Same-object/application weld into the selected R355/R357 coordinate.
    selectedMarkedDistanceIsCMP99Discrepancy :
      selectedMarkedDistance ≡ cmp99DiscrepancyDistance

open CMP99MarkedDistanceAttachment public

selectedMarkedBranch :
  (dataSet : CMP99MarkedDistanceAttachment) →
  collarRadius dataSet ≤ℝ selectedMarkedDistance dataSet
selectedMarkedBranch dataSet =
  subst
    (λ upper → collarRadius dataSet ≤ℝ upper)
    (sym (selectedMarkedDistanceIsCMP99Discrepancy dataSet))
    (sourceCollarBelowCMP99Discrepancy dataSet)

------------------------------------------------------------------------
-- Pareto/source accounting.
------------------------------------------------------------------------

cmp99MarkedDistanceTransportCompilerLevel : ProofLevel
cmp99MarkedDistanceTransportCompilerLevel = machineChecked

literalCMP99CollarDiscrepancyGeometryLevel : ProofLevel
literalCMP99CollarDiscrepancyGeometryLevel = conditional

selectedMarkedDistanceSameObjectAttachmentLevel : ProofLevel
selectedMarkedDistanceSameObjectAttachmentLevel = conditional

markedBranchIsOneOpaqueSourceLeaf : Bool
markedBranchIsOneOpaqueSourceLeaf = false

markedBranchIsOneOpaqueSourceLeafIsFalse :
  markedBranchIsOneOpaqueSourceLeaf ≡ false
markedBranchIsOneOpaqueSourceLeafIsFalse = refl

cmp99DiscrepancyMetricAutomaticallyEqualsSelectedMetric : Bool
cmp99DiscrepancyMetricAutomaticallyEqualsSelectedMetric = false

cmp99DiscrepancyMetricAutomaticallyEqualsSelectedMetricIsFalse :
  cmp99DiscrepancyMetricAutomaticallyEqualsSelectedMetric ≡ false
cmp99DiscrepancyMetricAutomaticallyEqualsSelectedMetricIsFalse = refl

record Round360Boundary : Set where
  constructor round360-boundary
  field
    transportCompilerOwned : Bool
    transportCompilerOwnedIsTrue : transportCompilerOwned ≡ true

    sourceCMP99GeometryStillOpen : Bool
    sourceCMP99GeometryStillOpenIsTrue : sourceCMP99GeometryStillOpen ≡ true

    selectedMetricAttachmentStillOpen : Bool
    selectedMetricAttachmentStillOpenIsTrue :
      selectedMetricAttachmentStillOpen ≡ true

canonicalRound360Boundary : Round360Boundary
canonicalRound360Boundary =
  round360-boundary true refl true refl true refl

round360FrontierRefinementLevel : ProofLevel
round360FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
