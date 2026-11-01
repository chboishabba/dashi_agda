module DASHI.Physics.YangMills.ZZRingBisectY13 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

pivot1 fourHundredEightyOneOver1379 : ℚ
pivot1 = + 1379 / 480
fourHundredEightyOneOver1379 = + 481 / 1379

idRaw : ∀ a b c →
  pivot1 * (b + fourHundredEightyOneOver1379 * c)
    * (b + fourHundredEightyOneOver1379 * c)
  ≡ pivot1 * (b + fourHundredEightyOneOver1379 * c)
    * (b + fourHundredEightyOneOver1379 * c)
idRaw = ℚRing.solve-∀
