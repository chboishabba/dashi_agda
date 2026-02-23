module DASHI.Algebra.BalancedTernary where

open import Agda.Builtin.Equality using (_≡_; refl)

data Trit : Set where
  neg zero pos : Trit

negate : Trit → Trit
negate neg = pos
negate pos = neg
negate zero = zero

