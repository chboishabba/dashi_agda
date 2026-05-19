module DASHI.Physics.Closure.TransportedPrimeCompatibilityProfile where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import DASHI.Physics.Closure.PrimeCompatibilityProfile as PCP

------------------------------------------------------------------------
-- Generic transported profile:
-- any state family equipped with a transported prime-address image can be
-- converted into the minimal closure-side compatibility profile by forgetting
-- multiplicity and remembering only whether each prime lane is present.

nonZero : Nat → Bool
nonZero zero = false
nonZero (suc _) = true

compatFromPrimeImage : FactorVec → SSP → Bool
compatFromPrimeImage (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) p with p
... | p2  = nonZero e2
... | p3  = nonZero e3
... | p5  = nonZero e5
... | p7  = nonZero e7
... | p11 = nonZero e11
... | p13 = nonZero e13
... | p17 = nonZero e17
... | p19 = nonZero e19
... | p23 = nonZero e23
... | p29 = nonZero e29
... | p31 = nonZero e31
... | p41 = nonZero e41
... | p47 = nonZero e47
... | p59 = nonZero e59
... | p71 = nonZero e71

transportedPrimeCompatibilityProfile :
  ∀ {ℓ} {State : Set ℓ} →
  (State → FactorVec) →
  PCP.PrimeCompatibilityProfile State
transportedPrimeCompatibilityProfile primeImage =
  record
    { compat = λ x p → compatFromPrimeImage (primeImage x) p
    }
