{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound328Exact where

------------------------------------------------------------------------
-- ROUND328 / SOURCE-NATIVE H1 DEBT RECLASSIFICATION
--
-- R323 correctly separated H1 from the other B coordinates, but still called
-- H1 the one B-side analytic producer debt.  R320/R322/R325/R327 sharpen the
-- source-native route further:
--
--   * CMP116 differentiated J-localization is already source-owned;
--   * normalized log-source -> connected covariance is compiler-owned;
--   * common-radius existence and selected domain membership are compiler-owned
--     once source demands are instantiated;
--   * the remaining task is SAME-OBJECT / SOURCE-APPLICATION: identify the
--     selected T5 J/density/root/support carrier with the published theorem's
--     carrier and apply that theorem there.
--
-- Therefore a fresh clustering inequality is NOT mandatory on this producer
-- route.  The direct R320 inequality remains the exact H1 consumer shape, while
-- its source-native payment is an application theorem rather than new analysis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact as R322
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound325Exact as R325
import DASHI.Physics.YangMills.BalabanCMP116SelectedJCommonDomainRound327Exact as R327
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source

-- The strongest current source-native compiler: once the selected physical
-- carrier is supplied as the actual common-domain instance of the published
-- theorem, H1 is obtained without introducing a second decay inequality.
sourceNativeApplicationPaysDirectH1 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  R327.SelectedJCommonDomainLocalization base →
  R320.DirectSelectedT5MarkedDecayPayment base
sourceNativeApplicationPaysDirectH1 =
  R327.commonDomainLocalizationBuildsR320Payment

record Round328Boundary : Set where
  constructor round328-boundary
  field
    publishedCMP116DifferentiatedLocalizationSourceOwned : Bool
    publishedCMP116DifferentiatedLocalizationSourceOwnedIsTrue :
      publishedCMP116DifferentiatedLocalizationSourceOwned ≡ true

    h1FreshAnalyticTheoremMandatoryOnSourceNativeRoute : Bool
    h1FreshAnalyticTheoremMandatoryOnSourceNativeRouteIsFalse :
      h1FreshAnalyticTheoremMandatoryOnSourceNativeRoute ≡ false

    h1SameObjectSourceApplicationStillRequired : Bool
    h1SameObjectSourceApplicationStillRequiredIsTrue :
      h1SameObjectSourceApplicationStillRequired ≡ true

    normalizedSourceCovarianceCalculusNeedsReproof : Bool
    normalizedSourceCovarianceCalculusNeedsReproofIsFalse :
      normalizedSourceCovarianceCalculusNeedsReproof ≡ false

    commonRadiusExistenceIndependentTheorem : Bool
    commonRadiusExistenceIndependentTheoremIsFalse :
      commonRadiusExistenceIndependentTheorem ≡ false

    freshClusteringInequalityRequiredAfterSourceApplication : Bool
    freshClusteringInequalityRequiredAfterSourceApplicationIsFalse :
      freshClusteringInequalityRequiredAfterSourceApplication ≡ false

    r327CompilesDirectlyToR320 : Bool
    r327CompilesDirectlyToR320IsTrue : r327CompilesDirectlyToR320 ≡ true

canonicalRound328Boundary : Round328Boundary
canonicalRound328Boundary =
  round328-boundary
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl

round328PublishedLocalizationLevel : ProofLevel
round328PublishedLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

-- This is the current source-native H1 residual.  It is intentionally kept
-- conditional: source ownership does not itself prove that the selected T5
-- carrier is the exact source carrier.
round328SelectedT5SourceApplicationLevel : ProofLevel
round328SelectedT5SourceApplicationLevel = conditional

round328SourceApplicationCompilerLevel : ProofLevel
round328SourceApplicationCompilerLevel = machineChecked

-- Historical J1/J2/J3 coordinates remain useful acquisition/debugging views,
-- but R325 already classifies them as source/application rather than fresh
-- analytic theorem debt.
round328PriorDebtClassificationLevel : ProofLevel
round328PriorDebtClassificationLevel = R325.round325ClassificationLevel

round328R322ApplicationCompilerLevel : ProofLevel
round328R322ApplicationCompilerLevel = R322.round322ApplicationCompilerLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
