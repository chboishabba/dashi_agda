module DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage where

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong)

open import DASHI.Physics.Constraints.Bracket using (LieLike)
open import DASHI.Physics.Constraints.Closure using (ClosureLaw)
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT

-- Transport data from a package carrier/bracket into the concrete CI carrier/bracket.
record ConstraintClosureTransport
  (P : CCGP.CanonicalConstraintGaugePackage) : Set₁ where
  field
    lift : CI.C → CCGP.Carrier P
    project : CCGP.Carrier P → CI.C
    project-lift : ∀ c → project (lift c) ≡ c
    bracket-compat :
      ∀ c₁ c₂ →
      project (CCGP._[_,]_ P (lift c₁) (lift c₂))
        ≡ LieLike._[_,]_ CI.L c₁ c₂

open ConstraintClosureTransport public

transportedClosureLaw :
  (P : CCGP.CanonicalConstraintGaugePackage) →
  ConstraintClosureTransport P →
  ClosureLaw CI.CS CI.L
transportedClosureLaw P T =
  record
    { closes = λ c₁ c₂ →
        let
          closeP = CCGP.closes P (lift T c₁) (lift T c₂)
          c₃P = fst closeP
          eqP = snd closeP
          lhs≡projBracket :
            LieLike._[_,]_ CI.L c₁ c₂
              ≡ project T (CCGP._[_,]_ P (lift T c₁) (lift T c₂))
          lhs≡projBracket = sym (bracket-compat T c₁ c₂)
          projBracket≡projC₃ :
            project T (CCGP._[_,]_ P (lift T c₁) (lift T c₂))
              ≡ project T c₃P
          projBracket≡projC₃ = cong (project T) eqP
        in
        project T c₃P , trans lhs≡projBracket projBracket≡projC₃
    }

canonicalConstraintClosureTransport :
  ConstraintClosureTransport PGCT.canonicalConstraintGaugePackage
canonicalConstraintClosureTransport =
  record
    { lift = λ c → c
    ; project = λ c → c
    ; project-lift = λ _ → refl
    ; bracket-compat = λ _ _ → refl
    }

-- Constraint closure derived from the canonical package
-- (instead of directly bundling CI.closure).
canonicalPackageInducedClosure :
  ClosureLaw CI.CS CI.L
canonicalPackageInducedClosure =
  transportedClosureLaw
    PGCT.canonicalConstraintGaugePackage
    canonicalConstraintClosureTransport
