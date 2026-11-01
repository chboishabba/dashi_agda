module DASHI.Physics.YangMills.ZZRingBisectC where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff)

minusOneThirtieth thirtyOneThirtieth fourHundredEightyOneOver1379 : ℚ
minusOneThirtieth = - (+ 1 / 30)
thirtyOneThirtieth = + 31 / 30
fourHundredEightyOneOver1379 = + 481 / 1379

idRaw : ∀ a b c →
  sqDiff b a
    + (sqDiff c b
    + sqDiff (- (a + (b + c + 0ℚ))) c)
  ≡ (+ 1 / 16) * (sq a + (sq b + (sq c + (sq (- (a + (b + c + 0ℚ))) + 0ℚ))))
    + (+ 15 / 8) * sq (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
    + (+ 1379 / 480) * sq (b + fourHundredEightyOneOver1379 * c)
    + (+ 13919 / 5516) * sq c
idRaw = ℚRing.solve-∀
