{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SignedRateBudgetWeldExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _/_; _≤_; _<_)
import Data.Rational.Properties as Q
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.List.Base using ([]; _∷_)
import DASHI.Physics.Closure.NSTriadKNR650Rational345LipschitzIntegralRound854Exact as R854

six twelve : ℚ
six = (+ 6) / 1
twelve = (+ 12) / 1

selected : ℚ → ℚ → ℚ → ℚ
selected C P D = six * (twelve * C - P + D)

-- Exact signed change; production is reversed, not absolutized.
selectedChange :
  ∀ C P D C₀ P₀ D₀ →
  selected C P D - selected C₀ P₀ D₀
    ≡ six * (twelve * (C - C₀) + (P₀ - P) + (D - D₀))
selectedChange C P D C₀ P₀ D₀ =
  solve (C ∷ P ∷ D ∷ C₀ ∷ P₀ ∷ D₀ ∷ [])

-- The original R853 selected rate is transported via its equality
-- to the literal normal form, rather than substituting a new observable.
sourceRateChange :
  ∀ r r₀ C P D C₀ P₀ D₀ →
  r ≡ selected C P D →
  r₀ ≡ selected C₀ P₀ D₀ →
  r - r₀ ≡ six * (twelve * (C - C₀) + (P₀ - P) + (D - D₀))
sourceRateChange r r₀ C P D C₀ P₀ D₀ h h₀
  rewrite h | h₀ = selectedChange C P D C₀ P₀ D₀

-- Direct endpoint weld: an actual source envelope on the original
-- selected rate, not a substituted or independently chosen initial rate.
sourceEndpointNegative :
  ∀ r → r ≤ R854.linearlyTransportedRateUpper854 → r < 0ℚ
sourceEndpointNegative r h =
  Q.≤-<-trans h R854.linearlyTransportedRateStrictlyNegative854
