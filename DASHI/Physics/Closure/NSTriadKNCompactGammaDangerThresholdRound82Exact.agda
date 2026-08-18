module DASHI.Physics.Closure.NSTriadKNCompactGammaDangerThresholdRound82Exact where

------------------------------------------------------------------------
-- ROUND82 / COMPACT-TRANSFER DANGER LEVEL
--
-- The preferred bounded C5 observable is the source-coupled compact transfer
-- potential
--
--   B = Gamma / (1 + Gamma)
--
-- on the resolved positive-transfer branch.  This file records the exact
-- division-free order statement needed by a deterministic occupation theorem.
-- If lambda <= Gamma, then
--
--   lambda (1 + Gamma) <= Gamma (1 + lambda).
--
-- With positive denominators this is precisely
--
--   lambda/(1+lambda) <= Gamma/(1+Gamma) = B.
--
-- The theorem below deliberately remains cross-multiplied: no reciprocal or
-- positivity premise is hidden in the algebraic core.  The real-valued
-- selected-trajectory realization may discharge positivity separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

compactThresholdCross : ℚ → ℚ → ℚ
compactThresholdCross lambda gamma = lambda * (1ℚ + gamma)

compactStateCross : ℚ → ℚ → ℚ
compactStateCross lambda gamma = gamma * (1ℚ + lambda)

compactificationOrderCrossDifference :
  ∀ lambda gamma →
  compactStateCross lambda gamma
  ≡ gamma + lambda * gamma
compactificationOrderCrossDifference lambda gamma =
  solve (lambda ∷ gamma ∷ [])

compactThresholdCrossExpansion :
  ∀ lambda gamma →
  compactThresholdCross lambda gamma
  ≡ lambda + lambda * gamma
compactThresholdCrossExpansion lambda gamma =
  solve (lambda ∷ gamma ∷ [])

dangerImpliesCompactLevelCrossBound :
  ∀ lambda gamma →
  lambda ≤ gamma →
  compactThresholdCross lambda gamma ≤ compactStateCross lambda gamma
dangerImpliesCompactLevelCrossBound lambda gamma danger =
  let
    raw : lambda + lambda * gamma ≤ gamma + lambda * gamma
    raw = ℚP.+-monoʳ-≤ (lambda * gamma) danger
  in
  subst
    (λ left → left ≤ compactStateCross lambda gamma)
    (sym (compactThresholdCrossExpansion lambda gamma))
    (subst
      (λ right → lambda + lambda * gamma ≤ right)
      (sym (compactificationOrderCrossDifference lambda gamma))
      raw)

record ResolvedCompactDangerLevel : Set where
  constructor resolved-compact-danger
  field
    threshold gamma : ℚ
    danger : threshold ≤ gamma

open ResolvedCompactDangerLevel public

resolvedDangerHasCompactCrossLevel :
  (datum : ResolvedCompactDangerLevel) →
  compactThresholdCross (threshold datum) (gamma datum)
  ≤ compactStateCross (threshold datum) (gamma datum)
resolvedDangerHasCompactCrossLevel datum =
  dangerImpliesCompactLevelCrossBound
    (threshold datum) (gamma datum) (danger datum)

round82DangerThresholdTransportsToCompactLevelDivisionFree : Bool
round82DangerThresholdTransportsToCompactLevelDivisionFree = true

round82DangerThresholdTransportsToCompactLevelDivisionFreeIsTrue :
  round82DangerThresholdTransportsToCompactLevelDivisionFree ≡ true
round82DangerThresholdTransportsToCompactLevelDivisionFreeIsTrue = refl
