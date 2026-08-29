{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact where

------------------------------------------------------------------------
-- ROUND106: CANONICAL METRIC-PERTURBATION -> CMP116 SOURCE DOMAIN
--
-- Round104 constructs a canonical positive radius from finitely many normalized
-- CMP116 demands.  Round103 records one common analytic radius, but its current
-- source-domain interface only carries evidence for the distinguished physical
-- coordinates; it does not say that an arbitrary metric-induced tangent lies in
-- the analytic ball merely because a radius number exists.
--
-- This owner makes the missing domain theorem exact.  The physical application
-- must provide the metric perturbation norm, the map into the literal source
-- tangent, and an evidence-bearing proof that every admitted perturbation lands
-- in the source-coordinate analytic domain at the SAME canonical radius.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain

record CanonicalMetricSourceDomain
    (Scale Volume : Set)
    (activity : Chain.SubstitutedActivitySecondVariation) : Set₁ where
  field
    demands : Canon.CMP116FiniteNormalizedAnalyticDemands
    radiusData : Radius.CMP116CommonAnalyticRadius Scale Volume

    -- The common source radius used by this application is literally the
    -- canonical Round104 choice, not a parallel neighbourhood.
    radiusIsCanonical :
      Radius.radius radiusData ≡ Canon.canonicalCommonRadius demands

    MetricPerturbation : Set
    metricPerturbationNorm : MetricPerturbation → ℚ

    AdmissibleMetricPerturbation : MetricPerturbation → Set
    admissibleMetricPerturbationBelowRadius :
      ∀ perturbation →
      AdmissibleMetricPerturbation perturbation →
      metricPerturbationNorm perturbation < Canon.canonicalCommonRadius demands

    metricPerturbationToBackgroundTangent :
      Chain.Background activity →
      MetricPerturbation → Chain.BackgroundTangent activity

    -- Evidence-bearing domain membership for the actual induced tangent.
    -- This is intentionally stronger than merely knowing `radius > 0`.
    SourceTangentInside :
      Scale → Volume → Chain.Background activity →
      Chain.BackgroundTangent activity → Set

    admittedMetricTangentInside :
      ∀ scale volume background perturbation →
      AdmissibleMetricPerturbation perturbation →
      SourceTangentInside scale volume background
        (metricPerturbationToBackgroundTangent background perturbation)

open CanonicalMetricSourceDomain public

canonicalMetricRadiusPositive :
  ∀ {Scale Volume activity}
    (dataSet : CanonicalMetricSourceDomain Scale Volume activity) →
  ℚ.0ℚ < Canon.canonicalCommonRadius (demands dataSet)
canonicalMetricRadiusPositive dataSet =
  Canon.canonicalCommonRadiusPositive (demands dataSet)

record CanonicalMetricSourceDomainBoundary : Set where
  constructor canonicalMetricSourceDomainBoundary
  field
    positiveRadiusAloneProvesMetricTangentMembership : Bool
    positiveRadiusAloneProvesMetricTangentMembershipIsFalse :
      positiveRadiusAloneProvesMetricTangentMembership ≡ false

    commonRadiusCoordinateWitnessAutomaticallyCoversEveryMetricTangent : Bool
    commonRadiusCoordinateWitnessAutomaticallyCoversEveryMetricTangentIsFalse :
      commonRadiusCoordinateWitnessAutomaticallyCoversEveryMetricTangent ≡ false

    explicitAdmissibilityPlusTangentMembershipIsSufficientDomainInterface : Bool
    explicitAdmissibilityPlusTangentMembershipIsSufficientDomainInterfaceIsTrue :
      explicitAdmissibilityPlusTangentMembershipIsSufficientDomainInterface ≡ true

canonicalMetricSourceDomainBoundary : CanonicalMetricSourceDomainBoundary
canonicalMetricSourceDomainBoundary =
  canonicalMetricSourceDomainBoundary false refl false refl true refl

canonicalMetricSourceDomainPackagingLevel : ProofLevel
canonicalMetricSourceDomainPackagingLevel = machineChecked

literalMetricPerturbationToCMP116SourceDomainLevel : ProofLevel
literalMetricPerturbationToCMP116SourceDomainLevel = conditional
