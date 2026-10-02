module DASHI.ComputerScience.TekumSpecialValuesExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem

tritEq : Trit.Trit → Trit.Trit → Bool
tritEq Trit.neg Trit.neg = true
tritEq Trit.neg _ = false
tritEq Trit.zer Trit.zer = true
tritEq Trit.zer _ = false
tritEq Trit.pos Trit.pos = true
tritEq Trit.pos _ = false

allSame : ∀ {n} → Trit.Trit → Vec Trit.Trit n → Bool
allSame t [] = true
allSame t (x ∷ xs) with tritEq t x
... | false = false
... | true = allSame t xs

classifySpecial : ∀ {n} → Vec Trit.Trit n → Maybe Sem.SpecialValue
classifySpecial xs with allSame Trit.neg xs
... | true = just Sem.naR
... | false with allSame Trit.zer xs
...   | true = just Sem.zeroValue
...   | false with allSame Trit.pos xs
...     | true = just Sem.infinity
...     | false = nothing

negativeSingletonIsNaR :
  classifySpecial (Trit.neg ∷ []) ≡ just Sem.naR
negativeSingletonIsNaR = refl

zeroSingletonIsZero :
  classifySpecial (Trit.zer ∷ []) ≡ just Sem.zeroValue
zeroSingletonIsZero = refl

positiveSingletonIsInfinity :
  classifySpecial (Trit.pos ∷ []) ≡ just Sem.infinity
positiveSingletonIsInfinity = refl

record TekumSpecialBoundary : Set where
  constructor tekumSpecialBoundary
  field
    allNegativeReservedForNaR : Bool
    allZeroReservedForZero : Bool
    allPositiveReservedForInfinity : Bool
    ordinaryWordsRemainOutsideTheseThreeCases : Bool

canonicalTekumSpecialBoundary : TekumSpecialBoundary
canonicalTekumSpecialBoundary =
  tekumSpecialBoundary true true true true
