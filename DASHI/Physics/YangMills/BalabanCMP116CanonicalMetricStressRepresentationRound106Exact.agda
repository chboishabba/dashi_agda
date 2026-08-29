{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact where

------------------------------------------------------------------------
-- ROUND106: STRESS REPRESENTATION ON THE CANONICAL CMP116 METRIC DOMAIN
--
-- The correct first-order theorem is functional, not an untyped identification
-- of a derivative with a tensor:
--
--   h admissible  ->  D_g V_eff[h] = <T , h>.
--
-- The admissible metric perturbations and their map into the literal CMP116
-- source tangent are owned by `CanonicalMetricSourceDomain`.  This file adds
-- only the representation theorem and keeps the pairing convention explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain

record CanonicalMetricStressRepresentation
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity) : Set₁ where
  field
    StressTensor : Set
    PairingScalar : Set

    stressTensor : StressTensor
    firstVariationReadout : ℝ → PairingScalar
    stressMetricPairing :
      StressTensor → Domain.MetricPerturbation domain → PairingScalar

    -- Literal first metric/source variation represented by the stress tensor on
    -- every perturbation admitted by the canonical source-domain theorem.
    firstVariationRepresentedByStress :
      ∀ background perturbation →
      Domain.AdmissibleMetricPerturbation domain perturbation →
      firstVariationReadout
        (First.substitutedFirstVariation activity background
          (Domain.metricPerturbationToBackgroundTangent
            domain background perturbation))
      ≡ stressMetricPairing stressTensor perturbation

open CanonicalMetricStressRepresentation public

admittedMetricVariationEqualsStressPairing :
  ∀ {Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    (representation : CanonicalMetricStressRepresentation domain) →
  ∀ background perturbation →
  Domain.AdmissibleMetricPerturbation domain perturbation →
  firstVariationReadout representation
    (First.substitutedFirstVariation activity background
      (Domain.metricPerturbationToBackgroundTangent
        domain background perturbation))
  ≡ stressMetricPairing representation
      (stressTensor representation) perturbation
admittedMetricVariationEqualsStressPairing representation =
  firstVariationRepresentedByStress representation

record CanonicalMetricStressRepresentationBoundary : Set where
  constructor canonicalMetricStressRepresentationBoundary
  field
    tensorNameAloneFixesMetricPairingConvention : Bool
    tensorNameAloneFixesMetricPairingConventionIsFalse :
      tensorNameAloneFixesMetricPairingConvention ≡ false

    stressRepresentationRequiredOutsideAdmittedAnalyticDomain : Bool
    stressRepresentationRequiredOutsideAdmittedAnalyticDomainIsFalse :
      stressRepresentationRequiredOutsideAdmittedAnalyticDomain ≡ false

    canonicalDomainPlusRepresentationIsExactFiniteCutoffStressSocket : Bool
    canonicalDomainPlusRepresentationIsExactFiniteCutoffStressSocketIsTrue :
      canonicalDomainPlusRepresentationIsExactFiniteCutoffStressSocket ≡ true

canonicalMetricStressRepresentationBoundary :
  CanonicalMetricStressRepresentationBoundary
canonicalMetricStressRepresentationBoundary =
  canonicalMetricStressRepresentationBoundary false refl false refl true refl

canonicalMetricStressRepresentationCompilerLevel : ProofLevel
canonicalMetricStressRepresentationCompilerLevel = machineChecked

literalCMP116MetricStressRepresentationLevel : ProofLevel
literalCMP116MetricStressRepresentationLevel = conditional
