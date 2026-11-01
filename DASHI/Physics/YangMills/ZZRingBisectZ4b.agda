module DASHI.Physics.YangMills.ZZRingBisectZ4b where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; _+_; _*_; _-_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

lastL : ℚ → ℚ
lastL l = l

path4LDLExpandedRaw : ∀ a b c →
  ((b - a) * (b - a)) + (((c - b) * (c - b))
    + ((- (a + (b + c)) - c) * (- (a + (b + c)) - c)))
  ≡ ((+ 1 / 16) * ((a * a) + ((b * b) + ((c * c)
      + ((- (a + (b + c))) * (- (a + (b + c))))))))
    + ((((+ 15 / 8) * (a + ((- (+ 1 / 30)) * b) + ((+ 31 / 30) * c))
        * (a + ((- (+ 1 / 30)) * b) + ((+ 31 / 30) * c)))
      + (((+ 1379 / 480) * (b + ((+ 481 / 1379) * c)) * (b + ((+ 481 / 1379) * c)))
      + ((+ 13919 / 5516) * (c * c)))))
path4LDLExpandedRaw = ℚRing.solve-∀
