module DASHI.Physics.Constructive.FiniteProductClusteringExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- DASHI CONTRIBUTION
--
-- Construct an exact two-site product measure.  For arbitrary observables F
-- and G on symmetric two-state sites, the joint expectation factors:
--
--   E[F G] = E[F] E[G].
--
-- Therefore the connected correlation vanishes exactly at every declared
-- positive separation.  This is stronger than exponential decay for this
-- independent finite model, but it is not OS4 clustering for an interacting
-- gauge measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record TwoStateObservable : Set where
  constructor twoStateObservable
  field
    plusValue minusValue : ℚ

open TwoStateObservable public

half : ℚ
half = 1ℚ /2
  where
    _/2 : ℚ → ℚ
    value /2 = value * (record { numerator = 1 ; denominator = 2 ; isCoprime = _ })
