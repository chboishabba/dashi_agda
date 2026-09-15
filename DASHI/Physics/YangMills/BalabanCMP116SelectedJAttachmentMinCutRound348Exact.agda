{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedJAttachmentMinCutRound348Exact where

------------------------------------------------------------------------
-- ROUND348 / SELECTED-J ATTACHMENT MIN-CUT
--
-- R347 correctly leaves a selected-J same-object attachment between the
-- source/Cauchy marked-boundary producer and R318's literal selected response.
-- This round removes one more false prerequisite from that attachment.
--
-- R318 already carries `LiteralTwoSourceInsertionMeaning`, and the generic
-- normalized two-source calculus proves on that exact carrier
--
--   D^2_{J(F),J(G)} log Z = Cov(F,G).
--
-- Therefore no fresh Yang--Mills theorem is needed to identify the selected
-- literal mixed-log derivative with the connected covariance once the selected
-- source directions are fixed.
--
-- The surviving physical/source application is narrower:
--
--   * attach R318's selected source directions J(F),J(G) to the literal CMP116
--     physical source-coordinate directions used by the marked boundary theorem;
--   * keep the SAME finite density/common analytic domain while doing so.
--
-- This file does not manufacture that physical coordinate/density attachment
-- and does not manufacture the R347 marked-boundary/substitution comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedBoundaryFrontierRound347Exact as R347

------------------------------------------------------------------------
-- Existing compiler, specialized to the exact unlocalized R318 carrier.
------------------------------------------------------------------------

selectedLiteralMixedLogDerivativeIsConnectedCovariance :
  ∀ {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  ∀ left right →
  Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
    (Cumulant.sourceDirectionOf (R318.meaning base) left)
    (Cumulant.sourceDirectionOf (R318.meaning base) right)
  ≡
  Cumulant.connectedCovariance
    (R295.t5FiniteExpectationAlgebra dataSet extension)
    left right
selectedLiteralMixedLogDerivativeIsConnectedCovariance base left right =
  Cumulant.literalMixedLogDerivativeIsConnectedCovariance
    (R318.meaning base) left right

------------------------------------------------------------------------
-- The actual selected-J source application that remains theorem-bearing.
------------------------------------------------------------------------

record SelectedJPhysicalSourceAttachment : Set₁ where
  constructor selected-j-physical-source-attachment
  field
    -- Physical same-object identification of R318's J(F),J(G) with the literal
    -- CMP116 source coordinates consumed by the selected boundary theorem.
    LiteralCMP116SelectedSourceCoordinates : Set
    literalCMP116SelectedSourceCoordinates : LiteralCMP116SelectedSourceCoordinates

    -- The coordinate identification must preserve the SAME finite density and
    -- the common analytic source domain; it cannot splice an unrelated source
    -- theorem into the selected T5 expectation family.
    SameDensityCommonDomainAttachment : Set
    sameDensityCommonDomainAttachment : SameDensityCommonDomainAttachment

open SelectedJPhysicalSourceAttachment public

------------------------------------------------------------------------
-- Proof-search / Pareto classification.
------------------------------------------------------------------------

genericTwoSourceConnectedCumulantLevel : ProofLevel
genericTwoSourceConnectedCumulantLevel =
  Cumulant.twoSourceConnectedCumulantCompilerLevel

normalizedLogSourceCalculusLevel : ProofLevel
normalizedLogSourceCalculusLevel =
  Cumulant.normalizedLogSourceCalculusLevel

selectedLiteralYMSourceInsertionMeaningLevel : ProofLevel
selectedLiteralYMSourceInsertionMeaningLevel =
  Cumulant.literalYMSourceInsertionMeaningLevel

selectedCMP116SourceCoordinateAttachmentLevel : ProofLevel
selectedCMP116SourceCoordinateAttachmentLevel = conditional

sameDensityCommonDomainAttachmentLevel : ProofLevel
sameDensityCommonDomainAttachmentLevel = conditional

selectedMarkedBoundarySubstitutionLevel : ProofLevel
selectedMarkedBoundarySubstitutionLevel =
  R347.selectedMarkedBoundarySubstitutionLevel

selectedDistanceTimeLevel : ProofLevel
selectedDistanceTimeLevel = R347.selectedDistanceTimeLevel

record Round348Boundary : Set where
  constructor round348-boundary
  field
    normalizedTwoSourceCalculusIsFreshYMAnalysis : Bool
    normalizedTwoSourceCalculusIsFreshYMAnalysisIsFalse :
      normalizedTwoSourceCalculusIsFreshYMAnalysis ≡ false

    selectedLiteralMixedLogToCovarianceNeedsReproof : Bool
    selectedLiteralMixedLogToCovarianceNeedsReproofIsFalse :
      selectedLiteralMixedLogToCovarianceNeedsReproof ≡ false

    selectedJAttachmentStillNeedsPhysicalSourceCoordinateWeld : Bool
    selectedJAttachmentStillNeedsPhysicalSourceCoordinateWeldIsTrue :
      selectedJAttachmentStillNeedsPhysicalSourceCoordinateWeld ≡ true

    selectedJAttachmentStillNeedsSameDensityCommonDomain : Bool
    selectedJAttachmentStillNeedsSameDensityCommonDomainIsTrue :
      selectedJAttachmentStillNeedsSameDensityCommonDomain ≡ true

    selectedBoundarySubstitutionStillProofBearing : Bool
    selectedBoundarySubstitutionStillProofBearingIsTrue :
      selectedBoundarySubstitutionStillProofBearing ≡ true

    selectedDistanceTimeStillProofBearing : Bool
    selectedDistanceTimeStillProofBearingIsTrue :
      selectedDistanceTimeStillProofBearing ≡ true

canonicalRound348Boundary : Round348Boundary
canonicalRound348Boundary =
  round348-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl

round348CompilerLevel : ProofLevel
round348CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
