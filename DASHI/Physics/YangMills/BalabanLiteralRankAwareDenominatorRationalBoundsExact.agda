module DASHI.Physics.YangMills.BalabanLiteralRankAwareDenominatorRationalBoundsExact where

-- The exact rational ARITHMETIC component of the source-normalized
-- lattice denominator bound. No analytic sine inequality is assumed
-- or invented: the caller must prove each axis's actual lower enclosure
-- is >= 2 for an outer axis or >= 0 for an inner axis.
-- This exports 2m for representatives of rank m, m=1,2,3,4.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _/_)
import Data.Rational.Properties as ℚP

two four six eight : ℚ
two = + 2 / 1
four = + 4 / 1
six = + 6 / 1
eight = + 8 / 1

sumFour : ℚ → ℚ → ℚ → ℚ → ℚ
sumFour a b c d = (a + b) + (c + d)

axisLower : Bool → ℚ
axisLower false = 0ℚ
axisLower true = two

rankMaskLower : Bool → Bool → Bool → Bool → ℚ
rankMaskLower a b c d =
  sumFour (axisLower a) (axisLower b)
          (axisLower c) (axisLower d)

-- One exact monolithic proof works for ALL 16 outer/inner masks.
-- No assumption about multiplication by a negative rational occurs.
allMasksFourAxisLowerBound :
  ∀ (a b c d : Bool) {u v w t : ℚ} →
  axisLower a ≤ u →
  axisLower b ≤ v →
  axisLower c ≤ w →
  axisLower d ≤ t →
  rankMaskLower a b c d ≤ sumFour u v w t
allMasksFourAxisLowerBound a b c d au bv cw dt =
  ℚP.+-mono-≤ (ℚP.+-mono-≤ au bv)
              (ℚP.+-mono-≤ cw dt)

-- Four canonical source-grid rank representatives, not fabricated
-- alternative orbit cells.
rank1ArithmeticLowerExact :
  rankMaskLower true false false false ≡ two
rank1ArithmeticLowerExact = refl

rank2ArithmeticLowerExact :
  rankMaskLower true true false false ≡ four
rank2ArithmeticLowerExact = refl

rank3ArithmeticLowerExact :
  rankMaskLower true true true false ≡ six
rank3ArithmeticLowerExact = refl

rank4ArithmeticLowerExact :
  rankMaskLower true true true true ≡ eight
rank4ArithmeticLowerExact = refl

-- Remaining external physical gates:
-- 1. The actual normalized physical momentum q=πx for this source.
-- 2. A verified sine-square lower bound 4 sin²(q/2) >= 2 on outer axes
--    and >= 0 on inner axes, expressed as rational interval enclosures.
-- 3. An exact identification of the selected denominator AST with the
--    sum of the four source-normalized axis contributions.
-- 4. Strict denominator positivity as a proof for each division node.
