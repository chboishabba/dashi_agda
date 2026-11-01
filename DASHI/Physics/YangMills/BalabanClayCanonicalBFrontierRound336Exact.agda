{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound336Exact where

------------------------------------------------------------------------
-- ROUND336 / DO NOT CHARGE SELECTED-J MEANING TWICE
--
-- R335 factors the selected-pair domain weld through CMP116's published
-- common-J-domain semantics.  Archaeology of the actual selected T5 carrier
-- exposes one bookkeeping overcount in the remaining prose frontier:
--
--   `UnlocalizedT5StateFamilyJPresentation` ALREADY carries
--
--     meaning : LiteralTwoSourceInsertionMeaning calculus SourceDirection
--
-- as a proof-bearing coordinate.  Therefore, once the unlocalized selected-T5
-- base exists, physical-observable -> literal-J meaning is not an additional
-- theorem after that base; it is a projection of the base itself.
--
-- This does NOT claim that constructing the base is free.  The literal YM
-- source-insertion meaning remains a physical/same-density construction
-- coordinate upstream of the base constructor.  The correction is only about
-- dependency placement.
--
-- The source-side common-domain seam is also kept honest.  CMP116 Sect. 1,
-- around (1.23)--(1.29), takes one common analytic U,J domain before summing the
-- localized differentiated terms.  The generic source ABI intentionally leaves
-- `AdmissibleSourcePair` abstract, so local source replay/alignment is still a
-- proof-bearing source-transcription coordinate; citation metadata alone does
-- not inhabit it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainSourceFactorRound335Exact as R335

------------------------------------------------------------------------
-- The selected-J same-object meaning is literally carried by the base.
------------------------------------------------------------------------

selectedJMeaningAlreadyCarriedByBase :
  ∀ {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  Cumulant.LiteralTwoSourceInsertionMeaning
    (R318.calculus base)
    (R318.SourceDirection base)
selectedJMeaningAlreadyCarriedByBase base = R318.meaning base

selectedJSourceDirectionAlreadyCarriedByBase :
  ∀ {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  TestObservable → R318.SourceDirection base
selectedJSourceDirectionAlreadyCarriedByBase base =
  Cumulant.sourceDirectionOf (R318.meaning base)

------------------------------------------------------------------------
-- Current dependency classification.
------------------------------------------------------------------------

record Round336Boundary : Set where
  constructor round336-boundary
  field
    selectedJMeaningIndependentTheoremAfterBase : Bool
    selectedJMeaningIndependentTheoremAfterBaseIsFalse :
      selectedJMeaningIndependentTheoremAfterBase ≡ false

    constructingBaseStillRequiresLiteralYMSourceMeaning : Bool
    constructingBaseStillRequiresLiteralYMSourceMeaningIsTrue :
      constructingBaseStillRequiresLiteralYMSourceMeaning ≡ true

    commonRadiusExistenceNeedsNewTheorem : Bool
    commonRadiusExistenceNeedsNewTheoremIsFalse :
      commonRadiusExistenceNeedsNewTheorem ≡ false

    commonJPairDomainReplayStillSourceFacing : Bool
    commonJPairDomainReplayStillSourceFacingIsTrue :
      commonJPairDomainReplayStillSourceFacing ≡ true

    commonJPairDomainReplayIsFreshYMDecayInequality : Bool
    commonJPairDomainReplayIsFreshYMDecayInequalityIsFalse :
      commonJPairDomainReplayIsFreshYMDecayInequality ≡ false

    r335CompilerRemainsValid : Bool
    r335CompilerRemainsValidIsTrue : r335CompilerRemainsValid ≡ true

canonicalRound336Boundary : Round336Boundary
canonicalRound336Boundary =
  round336-boundary
    false refl
    true refl
    false refl
    true refl
    false refl
    true refl

-- The published differentiated-localization statement is source-owned.  What
-- remains is local source-domain replay/alignment and physical base construction,
-- not a second clustering theorem.
round336PublishedLocalizationStatementLevel : ProofLevel
round336PublishedLocalizationStatementLevel =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

round336CommonRadiusCompilerLevel : ProofLevel
round336CommonRadiusCompilerLevel =
  R114.cmp116FiniteDemandsToCommonRadiusObjectLevel

round336CommonJPairDomainReplayLevel : ProofLevel
round336CommonJPairDomainReplayLevel =
  R335.round335PublishedCommonJPairDomainAuthorityLevel

round336LiteralYMSourceMeaningConstructionLevel : ProofLevel
round336LiteralYMSourceMeaningConstructionLevel =
  Cumulant.literalYMSourceInsertionMeaningLevel

round336DependencyCorrectionLevel : ProofLevel
round336DependencyCorrectionLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
