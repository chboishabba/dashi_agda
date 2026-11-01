module DASHI.Physics.YangMills.ZZRingBisectB7 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; -_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff)

idRaw : ∀ a b c →
  sq (b - a) + sqDiff c b ≡ sq (b - a) + sqDiff c b
idRaw = ℚRing.solve-∀
