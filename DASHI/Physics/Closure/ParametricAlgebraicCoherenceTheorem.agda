module DASHI.Physics.Closure.ParametricAlgebraicCoherenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Algebra.GaugeGroupContract as GGC
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem as PACT
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT

record ParametricAlgebraicCoherenceTheorem
  (P : CCGP.CanonicalConstraintGaugePackage) : Setω where
  field
    algebraicClosure : PACT.ParametricAlgebraicClosureTheorem P
    coherentBracketGauge :
      ∀ c₁ c₂ →
      CCGP.admissible P c₁ ≡ true →
      CCGP.admissible P c₂ ≡ true →
      GGC.Emergence.pickGauge
        (GGC.UniquenessClaim.E
          (PGCT.ParametricGaugeConstraintTheorem.uniqueness
            (PACT.ParametricAlgebraicClosureTheorem.gaugeTheorem
              algebraicClosure)))
        (CCGP._[_,]_ P c₁ c₂)
      ≡ GGC.SU3×SU2×U1

parametricAlgebraicCoherenceTheorem :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicCoherenceTheorem P
parametricAlgebraicCoherenceTheorem P =
  record
    { algebraicClosure = PACT.parametricAlgebraicClosureTheorem P
    ; coherentBracketGauge = λ c₁ c₂ a₁ a₂ →
        PACT.ParametricAlgebraicClosureTheorem.gaugeStableOnAdmissible
          (PACT.parametricAlgebraicClosureTheorem P)
          (CCGP._[_,]_ P c₁ c₂)
          (PACT.ParametricAlgebraicClosureTheorem.admissibilityClosed
            (PACT.parametricAlgebraicClosureTheorem P) c₁ c₂ a₁ a₂)
    }
