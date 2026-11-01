{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound325Exact where

------------------------------------------------------------------------
-- ROUND325 / SELECTED-J H1 DEBT-KIND CORRECTION
--
-- R323 established that H1 is the only current B-side quantitative producer
-- coordinate.  R324 then decomposed H1 into J1/J2/J3.  This round classifies
-- those three residuals by what they actually manufacture.
--
-- The key source fact is already owned by CMP116 source authority:
-- differentiated local activities on the declared common analytic J-domain
-- retain the source exponential/tree localization under finite Cauchy
-- differentiation.  Therefore J1/J2/J3 are NOT three fresh Yang--Mills
-- clustering inequalities.
--
--   J1 finite-demand extraction / coordinate identification
--      = source transcription + applicability on the literal active family.
--
--   J2 selected physical observable -> literal CMP116 J direction
--      = same-density semantic/application weld.
--
--   J3 connected two-J localized expansion on the same state/root/support
--      = source-theorem applicability / same-object weld.
--
-- Once those source/application coordinates are inhabited, R322 compiles the
-- published differentiated-localization theorem directly into R320's preferred
-- selected marked-decay payment.  R320 then feeds the existing clustering and
-- mass-gap compiler chain.
--
-- This does NOT claim those applicability/source welds are easy or already
-- inhabited.  It only prevents proof search from misclassifying them as three
-- independent new analytic estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound323Exact as R323
import DASHI.Physics.YangMills.BalabanCMP116SelectedJSourceMinCutRound324Exact as R324
import DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact as R322
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320

data SelectedJDebtKind325 : Set where
  sourceTranscriptionApplicabilityDebt : SelectedJDebtKind325
  sameObjectSemanticWeldDebt : SelectedJDebtKind325
  sourceTheoremApplicabilityDebt : SelectedJDebtKind325
  freshAnalyticProducerDebt : SelectedJDebtKind325

data SelectedJCoordinate325 : Set where
  j1FiniteDemandExtraction : SelectedJCoordinate325
  j2ObservableToJMeaning : SelectedJCoordinate325
  j3ConnectedTwoJLocalization : SelectedJCoordinate325

selectedJDebtKind325 : SelectedJCoordinate325 → SelectedJDebtKind325
selectedJDebtKind325 j1FiniteDemandExtraction = sourceTranscriptionApplicabilityDebt
selectedJDebtKind325 j2ObservableToJMeaning = sameObjectSemanticWeldDebt
selectedJDebtKind325 j3ConnectedTwoJLocalization = sourceTheoremApplicabilityDebt

-- All three remain real consumer-facing residuals until inhabited, but none is
-- classified here as a fresh analytic theorem.  The published localization
-- theorem is a source authority; the open work is application to the selected
-- physical carrier.
searchRole325 : SelectedJCoordinate325 → Introspective.ProofSearchTargetRole
searchRole325 j1FiniteDemandExtraction = Introspective.canonicalConsumerResidual
searchRole325 j2ObservableToJMeaning = Introspective.canonicalConsumerResidual
searchRole325 j3ConnectedTwoJLocalization = Introspective.canonicalConsumerResidual

record Round325Boundary : Set where
  constructor round325-boundary
  field
    cmp116DifferentiatedLocalizationSourceOwned : Bool
    cmp116DifferentiatedLocalizationSourceOwnedIsTrue :
      cmp116DifferentiatedLocalizationSourceOwned ≡ true

    j1FreshAnalyticTheorem : Bool
    j1FreshAnalyticTheoremIsFalse : j1FreshAnalyticTheorem ≡ false

    j2FreshAnalyticTheorem : Bool
    j2FreshAnalyticTheoremIsFalse : j2FreshAnalyticTheorem ≡ false

    j3FreshAnalyticTheorem : Bool
    j3FreshAnalyticTheoremIsFalse : j3FreshAnalyticTheorem ≡ false

    j1StillRequiresLiteralSourceExtraction : Bool
    j1StillRequiresLiteralSourceExtractionIsTrue :
      j1StillRequiresLiteralSourceExtraction ≡ true

    j2StillRequiresSameDensityObservableJMeaning : Bool
    j2StillRequiresSameDensityObservableJMeaningIsTrue :
      j2StillRequiresSameDensityObservableJMeaning ≡ true

    j3StillRequiresSameStateSourceApplicability : Bool
    j3StillRequiresSameStateSourceApplicabilityIsTrue :
      j3StillRequiresSameStateSourceApplicability ≡ true

    r322CompilesSourcePlusApplicabilityToR320 : Bool
    r322CompilesSourcePlusApplicabilityToR320IsTrue :
      r322CompilesSourcePlusApplicabilityToR320 ≡ true

    newIndependentClusteringInequalityRequiredAfterR322 : Bool
    newIndependentClusteringInequalityRequiredAfterR322IsFalse :
      newIndependentClusteringInequalityRequiredAfterR322 ≡ false

canonicalRound325Boundary : Round325Boundary
canonicalRound325Boundary =
  round325-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl

-- Revision-bound authoritative levels reused from the actual owners.
round325PublishedDifferentiatedLocalizationLevel : ProofLevel
round325PublishedDifferentiatedLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

round325J1Level : ProofLevel
round325J1Level = R324.round324J1CoordinateIdentificationLevel

round325J2Level : ProofLevel
round325J2Level = R324.round324J2LiteralSourceInsertionMeaningLevel

round325J3Level : ProofLevel
round325J3Level = R324.round324J3ConnectedTwoJLocalizationLevel

round325SelectedJDomainApplicationLevel : ProofLevel
round325SelectedJDomainApplicationLevel = R322.selectedJDomainApplicabilityLevel

round325R320PreferredPaymentLevel : ProofLevel
round325R320PreferredPaymentLevel = R320.round320DirectSelectedMarkedDecayLevel

round325H1IsOnlyBAnalyticProducerCoordinate : Bool
round325H1IsOnlyBAnalyticProducerCoordinate =
  R323.Round323Boundary.h1IsOnlyCurrentBAnalyticProducerDebt
    R323.canonicalRound323Boundary

round325ClassificationLevel : ProofLevel
round325ClassificationLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
