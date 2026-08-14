module DASHI.Physics.YangMills.ZZRingBisectB where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff)

idRaw : ∀ a b c →
  sqDiff b a
    + (sqDiff c b
    + sqDiff (- (a + (b + c))) c)
  ≡ (+ 1 / 16) * (sq a + (sq b + (sq c + sq (- (a + (b + c))))))
    + (+ 15 / 8) * sq (a + ((- (+ 1 / 30)) * b + ((+ 31 / 30) * c)))
    + (+ 1379 / 480) * sq (b + ((+ 481 / 1379) * c))
    + (+ 13919 / 5516) * sq c
idRaw = ℚRing.solve-∀
