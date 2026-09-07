module DASHI.Analysis.RiemannPlattTrudgianLowCompletionAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as Source

------------------------------------------------------------------------
-- PLATT--TRUDGIAN LOW-ORDINATE TRANSPORT
--
-- The published verified-height theorem and DASHI's AnalyticSubstrate live on
-- different carriers.  A citation or decimal height does not inhabit
-- `analyticCritical`.  The least-privilege bridge therefore asks only for:
--
--   * a predicate saying that THIS analytic zero lies in the published verified
--     region;
--   * an exact same-completed-zeta theorem taking that predicate to criticality;
--   * a proof that the chosen Low partition is contained in that region.
--
-- No high-side harmonic estimate is duplicated here.
------------------------------------------------------------------------

publishedVerifiedHeight : Nat
publishedVerifiedHeight = Source.plattTrudgianVerifiedHeight

record PlattTrudgianLowCriticalityTransport
    (analytic : Analytic.AnalyticSubstrate)
    (Low : Universal.AnalyticNontrivialZero analytic -> Set) : Set₁ where
  field
    WithinPublishedVerifiedHeight :
      Universal.AnalyticNontrivialZero analytic -> Set

    lowWithinPublishedVerifiedHeight :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low rho ->
      WithinPublishedVerifiedHeight rho

    publishedVerifiedHeightCritical :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      WithinPublishedVerifiedHeight rho ->
      Universal.analyticCritical rho

    sameCompletedZetaAsPublishedVerification : Set
    sameCompletedZetaAsPublishedVerificationReceipt :
      sameCompletedZetaAsPublishedVerification

    exactHeightReference : String
    transportReference : String

open PlattTrudgianLowCriticalityTransport public

compileLowCertifiedCritical :
  forall {analytic Low} ->
  PlattTrudgianLowCriticalityTransport analytic Low ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Low rho ->
  Universal.analyticCritical rho
compileLowCertifiedCritical transport rho low =
  publishedVerifiedHeightCritical transport rho
    (lowWithinPublishedVerifiedHeight transport rho low)

record PlattTrudgianLowCompletionBoundary : Set where
  constructor platt-trudgian-low-completion-boundary
  field
    publishedVerifiedHeightRecoveredInRepo : Bool
    publishedVerifiedHeightRecoveredInRepoIsTrue :
      publishedVerifiedHeightRecoveredInRepo ≡ true

    citationAloneInhabitsAnalyticCritical : Bool
    citationAloneInhabitsAnalyticCriticalIsFalse :
      citationAloneInhabitsAnalyticCritical ≡ false

    numericHeightAutomaticallyOrdersAbstractAnalyticReal : Bool
    numericHeightAutomaticallyOrdersAbstractAnalyticRealIsFalse :
      numericHeightAutomaticallyOrdersAbstractAnalyticReal ≡ false

    lowPartitionContainmentStillRequiresExactTransport : Bool
    lowPartitionContainmentStillRequiresExactTransportIsTrue :
      lowPartitionContainmentStillRequiresExactTransport ≡ true

    sameCompletedZetaIdentityStillRequired : Bool
    sameCompletedZetaIdentityStillRequiredIsTrue :
      sameCompletedZetaIdentityStillRequired ≡ true

    lowCriticalityCompilesAfterTransport : Bool
    lowCriticalityCompilesAfterTransportIsTrue :
      lowCriticalityCompilesAfterTransport ≡ true

    newHighOrdinateAnalysisManufacturedHere : Bool
    newHighOrdinateAnalysisManufacturedHereIsFalse :
      newHighOrdinateAnalysisManufacturedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalPlattTrudgianLowCompletionBoundary :
  PlattTrudgianLowCompletionBoundary
canonicalPlattTrudgianLowCompletionBoundary =
  platt-trudgian-low-completion-boundary
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The repo already recovers the Platt--Trudgian published verified height 3000175332800, but AnalyticSubstrate.Real is abstract. The low-side theorem therefore reduces to one exact carrier/source transport: identify a verified-height predicate on the same completed-zeta zero carrier, prove the chosen Low partition lies inside it, and transport the published criticality theorem. After those receipts, lowCertifiedCritical is compiler output. Citation alone is not a proof term and no high-side analysis is created here."
