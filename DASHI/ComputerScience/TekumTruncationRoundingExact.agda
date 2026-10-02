module DASHI.ComputerScience.TekumTruncationRoundingExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Vec using (Vec; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumFormalPropertiesExact as Formal

------------------------------------------------------------------------
-- Structural part of Proposition 5.
--
-- Words here are stored least-significant-trit first, so removing two head
-- trits is the exact counterpart of retaining a_{n-1}...a_2 in the paper.

truncateTwo :
  ∀ {n} → Vec Trit.Trit (suc (suc n)) → Vec Trit.Trit n
truncateTwo (a0 ∷ a1 ∷ rest) = rest

TekumTruncationRoundingWitness = Formal.TekumTruncationRoundingWitness
