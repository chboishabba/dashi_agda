{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact where

------------------------------------------------------------------------
-- ROUND106: CANONICAL METRIC-PERTURBATION -> CMP116 SOURCE DOMAIN
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)

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
  0ℚ < Canon.canonicalCommonRadius (demands dataSet)
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
