{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact where

------------------------------------------------------------------------
-- ROW A: CUBIC COUPLING BUDGET FROM POSITIVE INVERSE-SQUARE DRIFT
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- MATHEMATICAL ROLE
--
-- On the tuned asymptotically-free trajectory write u_j = g_j^{-2}.  A
-- positive beta margin implies, in the direction from ultraviolet to the
-- prescribed terminal coupling,
--
--       u_j - u_{j+1} >= bStar > 0.
--
-- Cross-multiplication gives the local cubic drift estimate
--
--       (bStar/2) g_j^3 <= g_{j+1} - g_j.
--
-- This file owns the nontrivial global consequence: those local inequalities
-- telescope, so the entire marginal history has a cutoff-independent CUBIC
-- budget
--
--       (bStar/2) sum_{j<K} g_j^3 <= g_K - g_0 <= gamma.
--
-- This is the natural shooting-sensitivity budget.  It replaces any false
-- assumption that sum g_j itself is uniformly bounded in K.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

half : ℚ
half = + 1 / 2

cube : ℚ → ℚ
cube g = (g * g) * g

data CouplingChain : Set where
  terminal : ℚ → CouplingChain
  _then_ : ℚ → CouplingChain → CouplingChain

first : CouplingChain → ℚ
first (terminal g) = g
first (g then rest) = g

last : CouplingChain → ℚ
last (terminal g) = g
last (_ then rest) = last rest

cubicHistory : CouplingChain → ℚ
cubicHistory (terminal g) = 0ℚ
cubicHistory (g then rest) = cube g + cubicHistory rest

data CubicDrift (bStar : ℚ) : CouplingChain → Set where
  done : ∀ g → CubicDrift bStar (terminal g)
  step : ∀ g {rest} →
    half * bStar * cube g ≤ first rest - g →
    CubicDrift bStar rest →
    CubicDrift bStar (g then rest)

cubicDriftTelescopes :
  ∀ {bStar chain} →
  CubicDrift bStar chain →
  half * bStar * cubicHistory chain ≤ last chain - first chain
cubicDriftTelescopes {bStar = bStar} {chain = terminal g} (done .g) =
  subst
    (λ right → 0ℚ ≤ right)
    (ℚRing.solve-∀ g)
    ℚP.≤-refl
cubicDriftTelescopes {bStar = bStar} {chain = g then rest}
    (step .g local restDrift) =
  let
    tail = cubicDriftTelescopes restDrift
    added = ℚP.+-mono-≤ local tail

    leftExact :
      (half * bStar * cube g)
        + (half * bStar * cubicHistory rest)
      ≡ half * bStar * cubicHistory (g then rest)
    leftExact = ℚRing.solve-∀ bStar g (cubicHistory rest)

    rightExact :
      (first rest - g) + (last rest - first rest)
      ≡ last (g then rest) - first (g then rest)
    rightExact = ℚRing.solve-∀ g (first rest) (last rest)
  in
  subst
    (λ lower → lower ≤ last (g then rest) - first (g then rest))
    leftExact
    (subst
      (λ upper →
        (half * bStar * cube g)
          + (half * bStar * cubicHistory rest)
        ≤ upper)
      rightExact
      added)

cubicHistoryBelowTerminalWindow :
  ∀ {bStar chain gamma} →
  CubicDrift bStar chain →
  0ℚ ≤ first chain →
  last chain ≤ gamma →
  half * bStar * cubicHistory chain ≤ gamma
cubicHistoryBelowTerminalWindow {chain = chain} drift firstNN terminalBelow =
  let
    telescoped = cubicDriftTelescopes drift

    differenceBelowLast : last chain - first chain ≤ last chain
    differenceBelowLast =
      subst
        (λ left → left ≤ last chain)
        (ℚRing.solve-∀ (last chain) (first chain))
        (ℚP.+-monoʳ-≤
          (last chain)
          (ℚP.neg-mono-≤ firstNN))
  in
  ℚP.≤-trans telescoped
    (ℚP.≤-trans differenceBelowLast terminalBelow)
