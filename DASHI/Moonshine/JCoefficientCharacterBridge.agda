module DASHI.Moonshine.JCoefficientCharacterBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Moonshine.MonsterCharacterTableExact as MCT

------------------------------------------------------------------------
-- The small, rigorous seam: an exact first-coefficient decomposition.
-- Possessing this record does not assert VOA construction, McKay--Thompson
-- correspondence, Hauptmodul status, or the Conway--Norton theorem.

record FirstMoonshineCoefficientBridge : Set where
  field
    table                : MCT.ExactMonsterCharacterTable
    trivialDimension     : Nat
    firstMonsterDegree   : Nat
    jCoefficient₁        : Nat
    coefficientIs196884 : jCoefficient₁ ≡ 196884
    firstDegreeIs196883 : firstMonsterDegree ≡ 196883
    decomposes           : jCoefficient₁ ≡ trivialDimension + firstMonsterDegree

firstCoefficientArithmetic : 196884 ≡ 1 + 196883
firstCoefficientArithmetic = refl

