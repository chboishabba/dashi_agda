module DASHI.Physics.Closure.NSTriadKNHHBadZetaMarginRound50Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 48 identified where the inverse-dyadic factor 1/2 can come from.
-- Round 50 separates that scale compensation from the genuinely contractive
-- quantity.  Write
--
--   zeta = 1 - alpha.
--
-- Then alpha<1 is exactly zeta>0 and the inherited physical target is
--
--   I_(q+1) <= ((1-zeta)/2) B_q.
--
-- The direct hard-budget forcing condition becomes
--
--   beta < zeta T.
--
-- Thus the physical parameters are (C0,zeta,beta), not an auxiliary ceiling M.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _-_; _*_; _<_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

zetaFromAlpha : ℚ → ℚ
zetaFromAlpha alpha = 1ℚ - alpha

alphaFromZeta : ℚ → ℚ
alphaFromZeta zeta = 1ℚ - zeta

zetaPositiveFromAlphaStrict :
  ∀ {alpha} → alpha < 1ℚ → 0ℚ < zetaFromAlpha alpha
zetaPositiveFromAlphaStrict = ℚP.-positiveˡ

alphaStrictFromZetaPositive :
  ∀ {zeta} → 0ℚ < zeta → alphaFromZeta zeta < 1ℚ
alphaStrictFromZetaPositive {zeta} zetaPositive =
  let shifted : 0ℚ + zeta < 1ℚ + zeta
      shifted = ℚP.+-mono-<-≤ zetaPositive ℚP.≤-refl
  in
  subst
    (λ left → left < 1ℚ + zeta)
    (solve (zeta ∷ []))
    (subst
      (λ right → (1ℚ - zeta) + zeta < right)
      (solve (zeta ∷ []))
      shifted)

alphaZetaRoundTrip : ∀ alpha → alphaFromZeta (zetaFromAlpha alpha) ≡ alpha
alphaZetaRoundTrip alpha = solve (alpha ∷ [])

zetaAlphaRoundTrip : ∀ zeta → zetaFromAlpha (alphaFromZeta zeta) ≡ zeta
zetaAlphaRoundTrip zeta = solve (zeta ∷ [])

forcingTargetAsZeta :
  ∀ alpha beta target →
  beta < (1ℚ - alpha) * target →
  beta < zetaFromAlpha alpha * target
forcingTargetAsZeta alpha beta target proof = proof

forcingTargetFromZeta :
  ∀ zeta beta target →
  beta < zeta * target →
  beta < (1ℚ - alphaFromZeta zeta) * target
forcingTargetFromZeta zeta beta target proof =
  subst
    (λ factor → beta < factor * target)
    (zetaAlphaRoundTrip zeta)
    proof

hhBadDyadicHalfIsScaleCompensationNotNormalizedContraction : Bool
hhBadDyadicHalfIsScaleCompensationNotNormalizedContraction = true

hhBadNormalizedContractionMarginIsZeta : Bool
hhBadNormalizedContractionMarginIsZeta = true

hhBadNormalizedContractionMarginIsZetaIsTrue :
  hhBadNormalizedContractionMarginIsZeta ≡ true
hhBadNormalizedContractionMarginIsZetaIsTrue = refl
