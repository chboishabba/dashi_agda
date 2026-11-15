module DASHI.Moonshine.JCoefficientCharacterBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import Data.Nat.Base as Nat
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



------------------------------------------------------------------------
-- EXACT P2 FIRST-COEFFICIENT 3-ADIC SCALE LEDGER.
--
-- These are finite literal Nat identities only. They do not assert
-- modular Hauptmodul realization, 194 Monster class traces, VOA
-- construction, or equality between j and a selected McKay-Thompson
-- function. The original character table remains its own authority.
------------------------------------------------------------------------

firstCoefficientThreeNineScaleExact :
  196884 ≡ (10 * (3 Nat.^ 9)) + 54
firstCoefficientThreeNineScaleExact = refl

firstCoefficientDivisibleByTwentySeven :
  196884 ≡ 27 * 7292
firstCoefficientDivisibleByTwentySeven = refl

firstCoefficientNotDivisibleByEightyOneRemainder :
  196884 ≡ (81 * 2430) + 54
firstCoefficientNotDivisibleByEightyOneRemainder = refl

firstCoefficientTrivialPlusFirstNontrivial :
  196884 ≡ 1 + 196883
firstCoefficientTrivialPlusFirstNontrivial = refl
