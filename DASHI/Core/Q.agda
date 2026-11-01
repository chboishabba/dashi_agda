module DASHI.Core.Q where

-- Re-export stdlib rationals as the project’s canonical ℚ.

open import Data.Rational as R using (ℚ; _+_; _-_; _*_; _/_; 0ℚ; 1ℚ)
open import Data.Rational.Properties as Rₚ using ()

-- Convenience aliases
_+ℚ_ = R._+_
_-ℚ_ = R._-_
_*ℚ_ = R._*_
zeroℚ = R.0ℚ
oneℚ  = R.1ℚ

open R public

-- Small numerals for convenience
twoℚ : ℚ
twoℚ = oneℚ +ℚ oneℚ

threeℚ : ℚ
threeℚ = twoℚ +ℚ oneℚ

fourℚ : ℚ
fourℚ = twoℚ +ℚ twoℚ
