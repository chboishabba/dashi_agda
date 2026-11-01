module DASHI.ComputerScience.TekumPrecisionCompositionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)
open import Data.Vec using (Vec; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumTruncationRoundingExact as Truncate

truncateFourDirect :
  ∀ {n} →
  Vec Trit.Trit (suc (suc (suc (suc n)))) →
  Vec Trit.Trit n
truncateFourDirect (a0 ∷ a1 ∷ a2 ∷ a3 ∷ rest) = rest

truncateTwoTwiceEqualsFour :
  ∀ {n}
  (xs : Vec Trit.Trit (suc (suc (suc (suc n))))) →
  Truncate.truncateTwo (Truncate.truncateTwo xs)
  ≡ truncateFourDirect xs
truncateTwoTwiceEqualsFour (a0 ∷ a1 ∷ a2 ∷ a3 ∷ rest) = refl
