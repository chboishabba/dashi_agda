{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanConnectedCollarSpanRound356Exact where

------------------------------------------------------------------------
-- ROUND356 / CONNECTED COLLAR EXIT -> LARGE LOCALISATION SPAN
--
-- R355 isolates the source coefficient-collar dichotomy.  Its large-X branch
-- should not be treated as a new analytic estimate: once a connected support
-- reaches from an anchor region to outside the enlarged coefficient collar,
-- ordinary graph-distance minimality gives
--
--   collarRadius <= graphDistance <= treePathLength <= treeSize.
--
-- `YMSupportGraphDistance` already uses this exact graph-theoretic direction in
-- the Step-V/P33 lane.  This owner extracts only the source-neutral ordered-Nat
-- compiler so the current CMP109/CMP99 route can reuse the geometry without
-- importing the stronger historical polymer producer.
--
-- The remaining physical payments are SAME-OBJECT / source application:
--   * map the literal CMP109 localization X to the support graph;
--   * prove exiting D^2 gives the required anchor-to-outside graph distance;
--   * identify the support-tree size with the CMP116 tree/localization length;
--   * calibrate block scale / coefficients for the weighted R355 large branch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat; _≤_)
open import Data.Nat.Properties using (≤-trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ConnectedCollarSpan : Set where
  field
    collarRadius : Nat
    graphDistance : Nat
    treePathLength : Nat
    treeSize : Nat

    collarExitDistance : collarRadius ≤ graphDistance
    graphDistanceBelowTreePath : graphDistance ≤ treePathLength
    treePathBelowTreeSize : treePathLength ≤ treeSize

open ConnectedCollarSpan public

connectedCollarExitForcesLargeTree :
  (dataSet : ConnectedCollarSpan) →
  collarRadius dataSet ≤ treeSize dataSet
connectedCollarExitForcesLargeTree dataSet =
  ≤-trans
    (collarExitDistance dataSet)
    (≤-trans
      (graphDistanceBelowTreePath dataSet)
      (treePathBelowTreeSize dataSet))

------------------------------------------------------------------------
-- Pareto / source accounting.
------------------------------------------------------------------------

connectedCollarSpanCompilerLevel : ProofLevel
connectedCollarSpanCompilerLevel = machineChecked

-- Source/application seams for the literal CMP109 localization family.
literalCMP109LocalizationSupportGraphAttachmentLevel : ProofLevel
literalCMP109LocalizationSupportGraphAttachmentLevel = conditional

literalCoefficientCollarExitDistanceLevel : ProofLevel
literalCoefficientCollarExitDistanceLevel = conditional

supportTreeSizeIsCMP116TreeLengthLevel : ProofLevel
supportTreeSizeIsCMP116TreeLengthLevel = conditional

-- R355's large branch is weighted and real-valued.  Converting the natural
-- span lower bound to
--
--   delta_collar * R + kappa' * treeLength <= kappa * treeLength
--
-- still requires the literal block-scale and coefficient calibration.  This is
-- deliberately not manufactured by the graph compiler.
r355LargeBranchWeightCalibrationLevel : ProofLevel
r355LargeBranchWeightCalibrationLevel = conditional

freshConnectednessTheoremRequired : Bool
freshConnectednessTheoremRequired = false

freshConnectednessTheoremRequiredIsFalse :
  freshConnectednessTheoremRequired ≡ false
freshConnectednessTheoremRequiredIsFalse = refl

supportGraphDistanceIsAutomaticallyCMP109SourceMetric : Bool
supportGraphDistanceIsAutomaticallyCMP109SourceMetric = false

supportGraphDistanceIsAutomaticallyCMP109SourceMetricIsFalse :
  supportGraphDistanceIsAutomaticallyCMP109SourceMetric ≡ false
supportGraphDistanceIsAutomaticallyCMP109SourceMetricIsFalse = refl

record Round356Boundary : Set where
  constructor round356-boundary
  field
    connectedSpanCompilerOwned : Bool
    connectedSpanCompilerOwnedIsTrue : connectedSpanCompilerOwned ≡ true

    cmp109SupportGraphAttachmentStillOpen : Bool
    cmp109SupportGraphAttachmentStillOpenIsTrue :
      cmp109SupportGraphAttachmentStillOpen ≡ true

    collarExitDistanceStillOpen : Bool
    collarExitDistanceStillOpenIsTrue : collarExitDistanceStillOpen ≡ true

    sourceTreeLengthAttachmentStillOpen : Bool
    sourceTreeLengthAttachmentStillOpenIsTrue :
      sourceTreeLengthAttachmentStillOpen ≡ true

    weightedLargeBranchCalibrationStillOpen : Bool
    weightedLargeBranchCalibrationStillOpenIsTrue :
      weightedLargeBranchCalibrationStillOpen ≡ true

canonicalRound356Boundary : Round356Boundary
canonicalRound356Boundary =
  round356-boundary
    true refl
    true refl
    true refl
    true refl
    true refl

round356FrontierRefinementLevel : ProofLevel
round356FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
