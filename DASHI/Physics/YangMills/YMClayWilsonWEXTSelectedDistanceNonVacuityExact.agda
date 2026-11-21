{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayWilsonWEXTSelectedDistanceNonVacuityExact where

------------------------------------------------------------------------
-- P0 ORIGINAL WEXT source-format regression: physical time is measured
-- by ONE SELECTED rooted-shell metric, not by *every* arbitrary metric.
--
-- The previous WilsonWEXTDownstreamSemantics contract had a field
--
--  (physicalDistance : Observable -> Observable -> Nat) ->
--  forall left right t ->
--    physicalDistance left (timeTranslate right t) == t
--
-- For ANY inhabited Observable this is impossible: choose distance=0
-- and t=1, demanding 0=1.  This theorem is a *proof* of that vacuity.
-- No choice of YM Hamiltonian, boundary, source or positivity repairs
-- a universal quantifier that is stronger than the physical theorem.
--
-- The canonical producer now indexes its time-distance equality by
-- its ORIGINAL selected physicalDistance; R332/OS1 and R349/R304
-- supply the existing geometrical source witnesses for that metric.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

universalTimeForEveryDistanceIsImpossible :
  ∀ {Observable : Set} →
  (originalWilsonWord : Observable) →
  (timeTranslate : Observable → Nat → Observable) →
  ((distance : Observable → Observable → Nat) →
    ∀ left right time →
      distance left (timeTranslate right time) ≡ time) →
  ⊥
universalTimeForEveryDistanceIsImpossible
    originalWilsonWord timeTranslate universal
  with universal
    (λ _ _ → zero)
    originalWilsonWord originalWilsonWord (suc zero)
... | ()

-- The same selected-metric obligation is entirely meaningful:
-- a fixed physical distance can be identified with Euclidean time
-- on admissible translated Wilson supports, as already formalised
-- by the original R332/R304 geometry.
