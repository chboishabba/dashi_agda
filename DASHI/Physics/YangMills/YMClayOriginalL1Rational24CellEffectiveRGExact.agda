{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOriginalL1Rational24CellEffectiveRGExact where

------------------------------------------------------------------------
-- ORIGINAL L=1 SU2 six-commutator quadratic Gibbs RG, exact Q source.
-- The independently checked original 24^4 finite law under the true
-- quaternion block B=U0*U1 has conditional moments
--   mu1(t) = 19/4 - t
--   mu2(t) = 4t²/3 - 169t/18 + 230/9, t=(Re B)².
-- This file checks the exact THREE-class rational effective density,
-- positive coarse weights and Z_T2 value in the native Q carrier.
--
-- The conditional-moment source bridge from the original 24^4 group
-- action to these scalar equations remains a separate Agda proof.
-- No new measure, classical pi, Bishop real cast or RG consistency
-- is assumed. This is a finite polynomial Taylor effective law,
-- NOT the full interacting exp Wilson/Bishop Haar.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; Positive)
import Data.Rational.Properties as ℚP

square : ℚ → ℚ
square t = t * t

half : ℚ
half = + 1 / 2

beta : ℚ
beta = + 1 / 96

conditionalFirst : ℚ → ℚ
conditionalFirst t = (+ 19 / 4) - t

conditionalSecond : ℚ → ℚ
conditionalSecond t =
  ((+ 4 / 3) * square t - (+ 169 / 18) * t) + (+ 230 / 9)

effectiveWeight : ℚ → ℚ
effectiveWeight t =
  (1ℚ - beta * conditionalFirst t)
    + ((beta * beta) * conditionalSecond t) * half

classZero classQuarter classOne : ℚ
classZero = 0ℚ
classQuarter = + 1 / 4
classOne = 1ℚ

zeroEffectiveExact :
  effectiveWeight classZero ≡ (+ 78955 / 82944)
zeroEffectiveExact = refl

quarterEffectiveExact :
  effectiveWeight classQuarter ≡ (+ 422191 / 442368)
quarterEffectiveExact = refl

oneEffectiveExact :
  effectiveWeight classOne ≡ (+ 35459 / 36864)
oneEffectiveExact = refl

zeroEffectivePositive : Positive (effectiveWeight classZero)
zeroEffectivePositive =
  subst Positive (sym zeroEffectiveExact)
    (ℚP.normalize-pos 78955 82944)

quarterEffectivePositive :
  Positive (effectiveWeight classQuarter)
quarterEffectivePositive =
  subst Positive (sym quarterEffectiveExact)
    (ℚP.normalize-pos 422191 442368)

oneEffectivePositive : Positive (effectiveWeight classOne)
oneEffectivePositive =
  subst Positive (sym oneEffectiveExact)
    (ℚP.normalize-pos 35459 36864)

-- Of the 24 original 24-cell group elements:
-- 6 have (Re B)^2 = 0; 16 have 1/4; 2 have 1.
coarseTotal : ℚ
coarseTotal =
  (((+ 6 / 1) * effectiveWeight classZero
    + (+ 16 / 1) * effectiveWeight classQuarter)
    + (+ 2 / 1) * effectiveWeight classOne) * (+ 1 / 24)

coarsePartitionExact :
  coarseTotal ≡ (+ 140731 / 147456)
coarsePartitionExact = refl

-- The equality to the original 24^4 source partition is a
-- genuine independent exact group/RG check:
-- scripts/check_ym_original_L1_24cell_induced_rg_20261117.py.
-- An Agda proof from the original noncommutative group table and
-- existing BalabanFiniteProbabilityPartitionDisintegrationExact
-- remains open. Do not call this a completed continuum cylinder.
