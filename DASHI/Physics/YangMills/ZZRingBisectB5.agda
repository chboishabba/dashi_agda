module DASHI.Physics.YangMills.ZZRingBisectB5 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; -_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq)

idRaw : ∀ a b c →
  sq (b - a) ≡ sq (b - a)
idRaw = ℚRing.solve-∀
