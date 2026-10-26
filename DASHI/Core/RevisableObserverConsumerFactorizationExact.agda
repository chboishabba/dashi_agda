module DASHI.Core.RevisableObserverConsumerFactorizationExact where

-- Original finite factorization proof by Johl Brown with ChatGPT assistance,
-- 2026-10-26. This is a thin consumer-facing lemma, not a new observer ontology.
-- Reuse: DASHI.Core.ObserverFactorizedRefinementExact,
-- DASHI.Core.ObserverRefinementFutureSafetyExact,
-- DASHI.Core.IntersectionalNonFactorability.
-- Historical background: Blackwell (1953), DOI 10.1214/aoms/1177729032;
-- Cousot and Cousot (1977), DOI 10.1145/512950.512973.
-- Source references do not constitute kernel or empirical authority.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

record ConsumerFactorization {History Observation Answer : Set}
    (observe : History → Observation)
    (answer : History → Answer) : Set where
  constructor consumerFactorization
  field
    decode : Observation → Answer
    factorizes : (h : History) → answer h ≡ decode (observe h)

open ConsumerFactorization public

sameObservationGivesSameAnswer :
  ∀ {H O A : Set} {observe : H → O} {answer : H → A} →
  ConsumerFactorization observe answer →
  (x y : H) → observe x ≡ observe y → answer x ≡ answer y
sameObservationGivesSameAnswer cert x y eq =
  trans (factorizes cert x)
    (trans (cong (decode cert) eq) (sym (factorizes cert y)))

collisionObstructsConsumerFactorization :
  ∀ {H O A : Set} {observe : H → O} {answer : H → A} →
  (x y : H) → observe x ≡ observe y →
  (answer x ≡ answer y → ⊥) →
  ConsumerFactorization observe answer → ⊥
collisionObstructsConsumerFactorization x y same distinct cert =
  distinct (sameObservationGivesSameAnswer cert x y same)

data TwoHistory : Set where first second : TwoHistory

coarse : TwoHistory → Nat
coarse _ = zero

fine : TwoHistory → Nat
fine first = zero
fine second = suc zero

zeroNotOne : zero ≡ suc zero → ⊥
zeroNotOne ()

toyNoDecoder : ConsumerFactorization coarse fine → ⊥
toyNoDecoder =
  collisionObstructsConsumerFactorization first second refl zeroNotOne

-- A source receipt is not a proof receipt; a finite counterexample is not
-- an empirical claim. Apply existing snowball attribution and proof-search
-- admission machinery at each consuming site.
