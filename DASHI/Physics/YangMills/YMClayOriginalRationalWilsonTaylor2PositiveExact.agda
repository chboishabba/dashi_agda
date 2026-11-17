module DASHI.Physics.YangMills.YMClayOriginalRationalWilsonTaylor2PositiveExact where

------------------------------------------------------------------------
-- Rational polynomial Gibbs input for ACTUAL original finite Wilson RG.
--
-- T2(S) = 1 - S + S²/2 = (1+(1-S)²)/2 > 0 for EVERY
-- rational action S. No "strict density" authority field, no
-- exponential-to-rational cast, no sign case distinction.
--
-- This source reuses the existing rational-square and positivity
-- proofs; transitive --safe cannot be asserted for those owners.
-- Its original Wilson fine-state / blocking consumer is the
-- pre-existing BalabanFiniteProbabilityPartitionDisintegrationExact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _/_; Positive; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact as Squares

half : ℚ
half = + 1 / 2

square : ℚ → ℚ
square value = value * value

taylor2 : ℚ → ℚ
taylor2 action =
  (1ℚ + square (1ℚ - action)) * half

taylor2StandardPolynomial :
  ∀ action →
  taylor2 action ≡
    1ℚ - action + (action * action) * half
taylor2StandardPolynomial = ℚRing.solve-∀

halfPositive : Positive half
halfPositive = ℚP.normalize-pos 1 2

onePlusSquarePositive :
  ∀ action → 0ℚ < 1ℚ + square (1ℚ - action)
onePlusSquarePositive action =
  subst
    (λ lower → lower < 1ℚ + square (1ℚ - action))
    (ℚRing.solve [])
    (ℚP.+-mono-<-≤
      (ℚP.positive⁻¹ 1ℚ)
      (Squares.squareNonnegative (1ℚ - action)))

taylor2Positive :
  ∀ action → Positive (taylor2 action)
taylor2Positive action =
  ℚP.pos*pos⇒pos
    (positive (onePlusSquarePositive action))
    halfPositive

-- This positive source applies to every original rational Wilson
-- deficit beta * sum_{six positive planes}(1 - trace), including
-- the true L=1 commutator cutoff. The original finite 24-cell
-- product construction and exact RG grouping are independently
-- verified in scripts/check_ym_original_L1_24cell_group_rg_20261117.py.
