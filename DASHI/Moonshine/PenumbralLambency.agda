module DASHI.Moonshine.PenumbralLambency where

-- Penumbral moonshine is indexed by a lambdency λ = (D₀ , ℓ).
-- The lambency ℓ consists of a level m together with a closed collection of
-- exact divisors encoding Atkin--Lehner involutions.  The discriminant and
-- genus/admissibility claims are proof-bearing parameters, not numerals baked
-- into the interface.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

record LambencyArithmetic : Set₁ where
  field
    ExactDivisor : Nat → Set
    oneExactDivisor : (m : Nat) → ExactDivisor m
    atkinLehnerProduct :
      (m : Nat) → ExactDivisor m → ExactDivisor m → ExactDivisor m
    frickeDivisor : (m : Nat) → ExactDivisor m

record Lambency
  (arithmetic : LambencyArithmetic) : Set₁ where
  field
    level : Nat
    involutionDivisors :
      LambencyArithmetic.ExactDivisor arithmetic level → Set

    containsIdentity :
      involutionDivisors
        (LambencyArithmetic.oneExactDivisor arithmetic level)

    closedUnderAtkinLehnerProduct :
      (a b : LambencyArithmetic.ExactDivisor arithmetic level) →
      involutionDivisors a →
      involutionDivisors b →
      involutionDivisors
        (LambencyArithmetic.atkinLehnerProduct arithmetic level a b)

    FuchsianGroup : Set
    representedGroup : FuchsianGroup
    GroupIsLambencyGroup : FuchsianGroup → Set
    representedGroupCorrect : GroupIsLambencyGroup representedGroup

    GenusZero : FuchsianGroup → Set
    genusZero : GenusZero representedGroup

isFricke :
  (arithmetic : LambencyArithmetic) →
  Lambency arithmetic → Set
isFricke arithmetic ell =
  Lambency.involutionDivisors ell
    (LambencyArithmetic.frickeDivisor arithmetic
      (Lambency.level ell))

record PenumbralLambdency
  (arithmetic : LambencyArithmetic)
  (Discriminant : Set) : Set₁ where
  field
    fundamentalDiscriminant : Discriminant
    lambency : Lambency arithmetic

    NegativeFundamental : Discriminant → Set
    negativeFundamental :
      NegativeFundamental fundamentalDiscriminant

    DiscriminantAdmissibleFor :
      Discriminant → Lambency arithmetic → Set
    discriminantAdmissible :
      DiscriminantAdmissibleFor fundamentalDiscriminant lambency

    fricke : isFricke arithmetic lambency

record PenumbralLambdencyBoundary : Set where
  field
    lambencyClosureRequired : ⊤
    genusZeroWitnessRequired : ⊤
    negativeFundamentalDiscriminantRequired : ⊤
    discriminantAdmissibilityRequired : ⊤
    noClassificationCompletenessClaim : ⊤

penumbralLambdencyBoundary : PenumbralLambdencyBoundary
penumbralLambdencyBoundary = record
  { lambencyClosureRequired = tt
  ; genusZeroWitnessRequired = tt
  ; negativeFundamentalDiscriminantRequired = tt
  ; discriminantAdmissibilityRequired = tt
  ; noClassificationCompletenessClaim = tt
  }
