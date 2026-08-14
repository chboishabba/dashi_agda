module DASHI.Physics.YangMills.ZZRingBisectY21 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _/_)

pivot2 : ℚ
pivot2 = + 13919 / 5516

idRaw : pivot2 + 0ℚ ≡ pivot2
idRaw = refl
