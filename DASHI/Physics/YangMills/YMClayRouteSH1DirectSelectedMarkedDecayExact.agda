{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanR318CanonicalDirectShellRound398Exact as R398
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedDecayToR274Round387Exact as R274Weld
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact as R322
import DASHI.Physics.YangMills.BalabanCMP116SelectedJCommonDomainRound327Exact as R327

------------------------------------------------------------------------
-- ROUTE-S H1 CANONICAL MIN-CUT
--
-- The historical H1 bookkeeping split the source payment into a published
-- localization object plus source-magnitude/root/distance applicability.
-- R320 is already the strictly smaller consumer-facing theorem on the exact
-- selected R318/T5 carrier:
--
--   magnitude (D^2 log Z)_selected
--       <= rootedShell(selected scale, volume, root, physicalDistance).
--
-- This module makes that one-field payment the canonical H1 boundary and
-- exposes the already-existing compiler chain:
--
--   R320 payment
--      -> localized R295 presentation
--      -> canonical exact finite T5 direct shell (R398/R284)
--      -> exact finite connected-covariance rooted shell (R274)
--      -> quantitative finite correlation-decay trajectory.
--
-- No source-envelope carrier, source-root equality, source-distance equality,
-- CMP109 polarization tensor, or independent direct-shell carrier is required
-- by the canonical H1 consumer.
------------------------------------------------------------------------

record RouteSH1DirectSelectedPayment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    directSelectedDecay : R320.DirectSelectedT5MarkedDecayPayment base

open RouteSH1DirectSelectedPayment public

h1BuildsLocalizedR295 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  RouteSH1DirectSelectedPayment base →
  R295.DirectT5StateFamilyJPresentation
    dataSet extension
h1BuildsLocalizedR295 base payment =
  R320.localizeBaseDirectlyAsR295 base (directSelectedDecay payment)

h1BuildsExactFiniteT5DirectShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  RouteSH1DirectSelectedPayment base →
  R284.DirectT5TwoSourceShell dataSet extension
h1BuildsExactFiniteT5DirectShell base payment =
  R398.canonicalDirectShell base (directSelectedDecay payment)

h1BuildsExactConnectedRootedShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  RouteSH1DirectSelectedPayment base →
  R274.TwoSourceConnectedRootedShellData
    (R318.Scale base) (R318.Volume base) (R318.Root base)
    Nat TestObservable
h1BuildsExactConnectedRootedShell base payment =
  R274Weld.r320PaymentAsR274ConnectedShell
    base (directSelectedDecay payment)

h1BuildsQuantitativeFiniteCorrelationDecay :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  RouteSH1DirectSelectedPayment base →
  Unified.QuantitativeCorrelationDecayTrajectory
h1BuildsQuantitativeFiniteCorrelationDecay base payment =
  R274Weld.r320PaymentBuildsQuantitativeCorrelationDecayTrajectory
    base (directSelectedDecay payment)

-- Existing stronger producer tactics factor through the canonical H1 object.

fromSelectedJDomainApplication :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  R322.CMP116SelectedJDomainApplication base →
  RouteSH1DirectSelectedPayment base
fromSelectedJDomainApplication application = record
  { directSelectedDecay =
      R322.selectedJDomainApplicationBuildsR320Payment application
  }

fromSelectedJCommonDomain :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  R327.SelectedJCommonDomainLocalization base →
  RouteSH1DirectSelectedPayment base
fromSelectedJCommonDomain source = record
  { directSelectedDecay =
      R327.commonDomainLocalizationBuildsR320Payment source
  }

------------------------------------------------------------------------
-- Pareto / frontier classification.
------------------------------------------------------------------------

canonicalH1HasOneTheoremBearingField : Bool
canonicalH1HasOneTheoremBearingField = true

canonicalH1HasOneTheoremBearingFieldIsTrue :
  canonicalH1HasOneTheoremBearingField ≡ true
canonicalH1HasOneTheoremBearingFieldIsTrue = refl

publishedLocalizationWrapperMandatoryForCanonicalH1 : Bool
publishedLocalizationWrapperMandatoryForCanonicalH1 = false

publishedLocalizationWrapperMandatoryForCanonicalH1IsFalse :
  publishedLocalizationWrapperMandatoryForCanonicalH1 ≡ false
publishedLocalizationWrapperMandatoryForCanonicalH1IsFalse = refl

sourceMagnitudeApplicabilityMandatoryForCanonicalH1 : Bool
sourceMagnitudeApplicabilityMandatoryForCanonicalH1 = false

sourceMagnitudeApplicabilityMandatoryForCanonicalH1IsFalse :
  sourceMagnitudeApplicabilityMandatoryForCanonicalH1 ≡ false
sourceMagnitudeApplicabilityMandatoryForCanonicalH1IsFalse = refl

sourceRootApplicabilityMandatoryForCanonicalH1 : Bool
sourceRootApplicabilityMandatoryForCanonicalH1 = false

sourceRootApplicabilityMandatoryForCanonicalH1IsFalse :
  sourceRootApplicabilityMandatoryForCanonicalH1 ≡ false
sourceRootApplicabilityMandatoryForCanonicalH1IsFalse = refl

sourceDistanceApplicabilityMandatoryForCanonicalH1 : Bool
sourceDistanceApplicabilityMandatoryForCanonicalH1 = false

sourceDistanceApplicabilityMandatoryForCanonicalH1IsFalse :
  sourceDistanceApplicabilityMandatoryForCanonicalH1 ≡ false
sourceDistanceApplicabilityMandatoryForCanonicalH1IsFalse = refl

independentDirectT5ShellMandatoryAfterH1 : Bool
independentDirectT5ShellMandatoryAfterH1 = false

independentDirectT5ShellMandatoryAfterH1IsFalse :
  independentDirectT5ShellMandatoryAfterH1 ≡ false
independentDirectT5ShellMandatoryAfterH1IsFalse = refl

h1NewAnalyticEstimateIntroduced : Bool
h1NewAnalyticEstimateIntroduced = false

h1NewAnalyticEstimateIntroducedIsFalse :
  h1NewAnalyticEstimateIntroduced ≡ false
h1NewAnalyticEstimateIntroducedIsFalse = refl

routeSH1PhysicalLevel : ProofLevel
routeSH1PhysicalLevel = R320.round320DirectSelectedMarkedDecayLevel

routeSH1CompilerLevel : ProofLevel
routeSH1CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
