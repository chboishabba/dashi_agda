{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedJApplicabilityMinCutRound326Exact where

------------------------------------------------------------------------
-- ROUND326 / LEAST-PRIVILEGE H1 SOURCE-APPLICATION ABI
--
-- R324 exposed three upstream coordinates J1/J2/J3.  R325 corrected their debt
-- kinds: they are source/application/same-object work, not three fresh analytic
-- clustering theorems.
--
-- For the actual H1 consumer, R322 already provides a smaller acquisition ABI:
--
--   * source theorem on the declared admissible CMP116 J-pair domain;
--   * proof that the selected T5 J-pair belongs to that domain.
--
-- From those two coordinates R322 constructs R320's exact selected marked-decay
-- payment.  Therefore this round makes the R322 application package the
-- preferred source-facing min-cut.  J1/J2/J3 remain upstream ways of building
-- that package; they are not scheduled as independent analytic leaves.
--
-- Nothing here claims the selected-J admissibility witness is already inhabited.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact as R322
import DASHI.Physics.YangMills.BalabanCMP116SelectedJSourceMinCutRound324Exact as R324
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound325Exact as R325
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source

data H1AcquisitionCoordinate326 : Set where
  publishedCMP116JLocalization : H1AcquisitionCoordinate326
  selectedJPairApplicability : H1AcquisitionCoordinate326

searchRole326 : H1AcquisitionCoordinate326 → Introspective.ProofSearchTargetRole
searchRole326 publishedCMP116JLocalization = Introspective.compilerConsequence
searchRole326 selectedJPairApplicability = Introspective.canonicalConsumerResidual

record Round326Boundary : Set where
  constructor round326-boundary
  field
    preferredH1SourceFacingCoordinates : Bool
    preferredH1SourceFacingCoordinatesIsTwo :
      preferredH1SourceFacingCoordinates ≡ true

    publishedLocalizationFreshYMAnalysis : Bool
    publishedLocalizationFreshYMAnalysisIsFalse :
      publishedLocalizationFreshYMAnalysis ≡ false

    selectedJApplicabilityStillOpen : Bool
    selectedJApplicabilityStillOpenIsTrue :
      selectedJApplicabilityStillOpen ≡ true

    j1J2J3RemainIndependentAnalyticLeaves : Bool
    j1J2J3RemainIndependentAnalyticLeavesIsFalse :
      j1J2J3RemainIndependentAnalyticLeaves ≡ false

    r322ApplicationBuildsR320Payment : Bool
    r322ApplicationBuildsR320PaymentIsTrue :
      r322ApplicationBuildsR320Payment ≡ true

    freshClusteringInequalityRequiredAfterApplication : Bool
    freshClusteringInequalityRequiredAfterApplicationIsFalse :
      freshClusteringInequalityRequiredAfterApplication ≡ false

canonicalRound326Boundary : Round326Boundary
canonicalRound326Boundary =
  round326-boundary
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl

-- Actual compiler: the preferred source/application package already *is* the
-- exact object R322 knows how to consume.  No additional analytic theorem is
-- inserted here.
compileSelectedJApplicationToR320 :
  ∀ {Measure TestObservable}
    {dataSet :
      DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact.PhysicalMeasureConvergenceData
        Measure TestObservable Data.Rational.Base.ℚ}
    {extension :
      DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact.ScalarCovarianceConvergenceExtension
        dataSet}
    {base :
      DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact.UnlocalizedT5StateFamilyJPresentation
        dataSet extension} →
  R322.CMP116SelectedJDomainApplication base →
  R320.DirectSelectedT5MarkedDecayPayment base
compileSelectedJApplicationToR320 =
  R322.selectedJDomainApplicationBuildsR320Payment

round326PublishedSourceLevel : ProofLevel
round326PublishedSourceLevel = Source.cmp116DifferentiatedActivityLocalizationLevel

round326SelectedJApplicabilityLevel : ProofLevel
round326SelectedJApplicabilityLevel = R322.selectedJDomainApplicabilityLevel

round326CompilerLevel : ProofLevel
round326CompilerLevel = machineChecked

-- Upstream coordinates are retained for acquisition/debugging, not promoted to
-- independent analytic theorem count.
round326J1Level : ProofLevel
round326J1Level = R324.round324J1CoordinateIdentificationLevel

round326J2Level : ProofLevel
round326J2Level = R324.round324J2LiteralSourceInsertionMeaningLevel

round326J3Level : ProofLevel
round326J3Level = R324.round324J3ConnectedTwoJLocalizationLevel

round326R325ClassificationLevel : ProofLevel
round326R325ClassificationLevel = R325.round325ClassificationLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
