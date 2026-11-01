module DASHI.Physics.Closure.ParametricAlgebraicClosureBundleTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem as PACT
open import DASHI.Physics.Closure.ParametricAlgebraicCoherenceTheorem as PACTC
open import DASHI.Physics.Closure.ParametricAlgebraicStabilityTheorem as PACTS

record ParametricAlgebraicClosureBundleTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    closure : PACT.ParametricAlgebraicClosureTheorem P
    coherence : PACTC.ParametricAlgebraicCoherenceTheorem P
    stability : PACTS.ParametricAlgebraicStabilityTheorem P

parametricAlgebraicClosureBundleTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicClosureBundleTheorem P
parametricAlgebraicClosureBundleTheorem P =
  record
    { closure = PACT.parametricAlgebraicClosureTheorem P
    ; coherence = PACTC.parametricAlgebraicCoherenceTheorem P
    ; stability = PACTS.parametricAlgebraicStabilityTheorem P
    }
