module DASHI.Physics.YangMills.ZZRingBisectY20 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)

pivot2 : ℚ
pivot2 = + 13919 / 5516

idRaw : pivot2 ≡ pivot2
idRaw = refl
