module DASHI.Physics.Closure.ParametricAlgebraicStabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicCoherenceTheorem as PACTC
open import DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem as PACT
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT

record ParametricAlgebraicStabilityTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    algebraicCoherence : PACTC.ParametricAlgebraicCoherenceTheorem P
    stableGaugeLeft :
      ∀ c →
      CCGP.admissible P c ≡ true →
      GGC.Emergence.pickGauge
        (GGC.UniquenessClaim.E
          (PGCT.ParametricGaugeConstraintTheorem.uniqueness
            (PACT.ParametricAlgebraicClosureTheorem.gaugeTheorem
              (PACTC.ParametricAlgebraicCoherenceTheorem.algebraicClosure
                algebraicCoherence)))) c
      ≡ GGC.SU3×SU2×U1
    stableGaugeRight :
      ∀ c →
      CCGP.admissible P c ≡ true →
      GGC.Emergence.pickGauge
        (GGC.UniquenessClaim.E
          (PGCT.ParametricGaugeConstraintTheorem.uniqueness
            (PACT.ParametricAlgebraicClosureTheorem.gaugeTheorem
              (PACTC.ParametricAlgebraicCoherenceTheorem.algebraicClosure
                algebraicCoherence)))) c
      ≡ GGC.SU3×SU2×U1

parametricAlgebraicStabilityTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicStabilityTheorem P
parametricAlgebraicStabilityTheorem P =
  record
    { algebraicCoherence = PACTC.parametricAlgebraicCoherenceTheorem P
    ; stableGaugeLeft = λ c a →
        PACT.ParametricAlgebraicClosureTheorem.gaugeStableOnAdmissible
          (PACTC.ParametricAlgebraicCoherenceTheorem.algebraicClosure
            (PACTC.parametricAlgebraicCoherenceTheorem P))
          c a
    ; stableGaugeRight = λ c a →
        PACT.ParametricAlgebraicClosureTheorem.gaugeStableOnAdmissible
          (PACTC.ParametricAlgebraicCoherenceTheorem.algebraicClosure
            (PACTC.parametricAlgebraicCoherenceTheorem P))
          c a
    }
