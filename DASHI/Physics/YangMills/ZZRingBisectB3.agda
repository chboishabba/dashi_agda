module DASHI.Physics.YangMills.ZZRingBisectB3 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff)

idRaw : ∀ a b c →
  sqDiff b a ≡ sqDiff b a
idRaw = ℚRing.solve-∀
