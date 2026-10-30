module DASHI.Foundations.PolynomialDoubleCommutatorSolvableNoGoExact where

------------------------------------------------------------------------
-- STRUCTURAL FINITE-DERIVED-LENGTH OBSTRUCTION FROM THE VIDEO'S
-- QUINTIC OVERLAPPING 3-CYCLE DOUBLE COMMUTATOR RECOVERY.
--
-- Classical derived series: Galois (1830-32), Jordan (1870).
-- Specific witness originally owned by:
--   QuinticOverlappingThreeCyclesExact.doubleCommutatorRecoversA/B
--
-- Unlike the previous 120-table enumeration, the theorem below
-- QUANTIFIES over EVERY finite derived length, not only finite tests.
-- Its inputs include BOTH inverse closure and actual nested identities.
-- No direct inference of same-object A5, actual generic polynomial
-- Galois group, radical formula, or Monster 3B from two witnesses.
--
-- Source-written proof; Agda compiler/kernel result PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

record SolvableCommutatorAlgebra : Set₁ where
  field
    Carrier : Set
    identity : Carrier
    inverse : Carrier → Carrier
    bracket : Carrier → Carrier → Carrier
    Derived : Nat → Carrier → Set
    derivedAll : (x : Carrier) → Derived zero x
    derivedInverse : (n : Nat) (x : Carrier) →
      Derived n x → Derived n (inverse x)
    derivedBracket : (n : Nat) (x y : Carrier) →
      Derived n x → Derived n y →
      Derived (suc n) (bracket x y)
    derivedLength : Nat
    derivedTerminates : (x : Carrier) →
      Derived derivedLength x → x ≡ identity

open SolvableCommutatorAlgebra public

record RecoveringPair (G : SolvableCommutatorAlgebra) : Set where
  field
    a b : Carrier G
    recoverA :
      bracket G
        (bracket G a b)
        (bracket G (inverse G a) (inverse G b)) ≡ a
    recoverB :
      bracket G
        (bracket G b a)
        (bracket G (inverse G b) (inverse G a)) ≡ b

open RecoveringPair public

-- Two layers of the derived series are gained by each recovery.
-- Use the predecessor step n to prove both target generators at
-- level (suc (suc n)), with NO termination or positivity escape.
recoveringPairGainsTwoLevels :
  (G : SolvableCommutatorAlgebra) (pair : RecoveringPair G) →
  (n : Nat) →
  Derived G n (a pair) →
  Derived G n (b pair) →
  Derived G (suc (suc n)) (a pair) ×
  Derived G (suc (suc n)) (b pair)
recoveringPairGainsTwoLevels G pair n da db =
  subst (Derived G (suc (suc n))) (recoverA pair)
    (derivedBracket G (suc n)
      (bracket G (a pair) (b pair))
      (bracket G (inverse G (a pair)) (inverse G (b pair)))
      (derivedBracket G n (a pair) (b pair) da db)
      (derivedBracket G n (inverse G (a pair)) (inverse G (b pair))
        (derivedInverse G n (a pair) da)
        (derivedInverse G n (b pair) db))) ,
  subst (Derived G (suc (suc n))) (recoverB pair)
    (derivedBracket G (suc n)
      (bracket G (b pair) (a pair))
      (bracket G (inverse G (b pair)) (inverse G (a pair)))
      (derivedBracket G n (b pair) (a pair) db da)
      (derivedBracket G n (inverse G (b pair)) (inverse G (a pair))
        (derivedInverse G n (b pair) db)
        (derivedInverse G n (a pair) da)))

-- To address odd derived levels we need the standard monotonicity
-- property of the derived filtration. This is an EXPLICIT field rather
-- than an implicit assumption about arbitrary subset families.
record StandardDerivedFiltration (G : SolvableCommutatorAlgebra) : Set₁ where
  field
    descendantIncluded :
      (n : Nat) (x : Carrier G) →
      Derived G (suc n) x → Derived G n x

open StandardDerivedFiltration public

atEveryDerivedLevel :
  (G : SolvableCommutatorAlgebra)
  (filtration : StandardDerivedFiltration G)
  (pair : RecoveringPair G)
  (n : Nat) →
  Derived G n (a pair) × Derived G n (b pair)
atEveryDerivedLevel G filtration pair zero =
  derivedAll G (a pair) , derivedAll G (b pair)
atEveryDerivedLevel G filtration pair (suc zero) =
  let doubled =
        recoveringPairGainsTwoLevels G pair zero
          (derivedAll G (a pair)) (derivedAll G (b pair))
  in descendantIncluded filtration 1 (a pair) (proj₁ doubled) ,
     descendantIncluded filtration 1 (b pair) (proj₂ doubled)
atEveryDerivedLevel G filtration pair (suc (suc n)) =
  let previous = atEveryDerivedLevel G filtration pair n
  in recoveringPairGainsTwoLevels G pair n
       (proj₁ previous) (proj₂ previous)

everySolvableRecoveringPairIsTrivial :
  (G : SolvableCommutatorAlgebra)
  (filtration : StandardDerivedFiltration G)
  (pair : RecoveringPair G) →
  a pair ≡ identity G × b pair ≡ identity G
everySolvableRecoveringPairIsTrivial G filtration pair =
  let terminal = atEveryDerivedLevel G filtration pair
                  (derivedLength G)
  in derivedTerminates G (a pair) (proj₁ terminal) ,
     derivedTerminates G (b pair) (proj₂ terminal)
