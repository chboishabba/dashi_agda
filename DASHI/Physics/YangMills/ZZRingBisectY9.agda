module DASHI.Physics.YangMills.ZZRingBisectY9 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

oneSixteenth pivot0 pivot1 pivot2 : ℚ
oneSixteenth = + 1 / 16
pivot0 = + 15 / 8
pivot1 = + 1379 / 480
pivot2 = + 13919 / 5516

minusOneThirtieth thirtyOneThirtieth fourHundredEightyOneOver1379 : ℚ
minusOneThirtieth = - (+ 1 / 30)
thirtyOneThirtieth = + 31 / 30
fourHundredEightyOneOver1379 = + 481 / 1379

idRaw : ∀ a b c →
  oneSixteenth * (a * a + (b * b + (c * c + (-(a + (b + c))) * (-(a + (b + c))))))
    + (pivot0 * (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
        * (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
    + (pivot1 * (b + fourHundredEightyOneOver1379 * c)
        * (b + fourHundredEightyOneOver1379 * c)
    + (pivot2 * (c * c) + 0ℚ)))
  ≡ oneSixteenth * (a * a + (b * b + (c * c + (-(a + (b + c))) * (-(a + (b + c))))))
    + (pivot0 * (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
        * (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
    + (pivot1 * (b + fourHundredEightyOneOver1379 * c)
        * (b + fourHundredEightyOneOver1379 * c)
    + (pivot2 * (c * c) + 0ℚ)))
idRaw = ℚRing.solve-∀
