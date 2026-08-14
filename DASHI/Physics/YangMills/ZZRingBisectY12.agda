module DASHI.Physics.YangMills.ZZRingBisectY12 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

pivot0 minusOneThirtieth thirtyOneThirtieth : ℚ
pivot0 = + 15 / 8
minusOneThirtieth = - (+ 1 / 30)
thirtyOneThirtieth = + 31 / 30

idRaw : ∀ a b c →
  pivot0 * (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
    * (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
  ≡ pivot0 * (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
    * (a + (minusOneThirtieth * b + thirtyOneThirtieth * c))
idRaw = ℚRing.solve-∀
