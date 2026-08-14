module DASHI.Physics.YangMills.ZZRingBisectBig where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; _+_; _*_; _-_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

bigLemma : ∀ a b c →
  ((+ 4514842591049713 / 240833315580756192) * (a + b) + c)
  ≡ ((+ 4514842591049713 / 240833315580756192) * a
      + ((+ 4514842591049713 / 240833315580756192) * b + c))
bigLemma = ℚRing.solve-∀
