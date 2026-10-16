module DASHI.Mathematics.Complexity.GuardedCookFiniteBitTableSelfCodeNoGoExact where

------------------------------------------------------------------------
-- FULL-TABLE-BAKED OWN-COOK GENERATOR CANNOT BE ITS OWN DESCRIBED MACHINE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact as Cursor
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookFiniteBitTableGeneratorExact as Table
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupExact as Lookup
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinStateWidthLowerExact as StateLower

mapFinSucLength :
  ∀ {n : Nat} (xs : List (Fin.Fin n)) →
  Canonical.listLength (Coded.mapFinSuc xs) ≡ Canonical.listLength xs
mapFinSucLength [] = refl
mapFinSucLength (x ∷ xs)
  rewrite mapFinSucLength xs = refl

allFinLength :
  (n : Nat) → Canonical.listLength (Coded.allFin n) ≡ n
allFinLength zero = refl
allFinLength (suc n)
  rewrite mapFinSucLength (Coded.allFin n)
        | allFinLength n = refl

codedStateWidthExact :
  (code : Coded.CodedFiniteStandardTM) →
  Canonical.StateWidth
    (Presented.finitePresentedStandardToConcrete
      (Coded.decodeCodedStandardTM code))
  ≡ Coded.stateCount code
codedStateWidthExact code = allFinLength (Coded.stateCount code)

lookupStateCountExact :
  (n : Nat) →
  (bits : Fin.Fin n → Bool) →
  Coded.stateCount (Lookup.lookupCode n bits)
  ≡ suc n + suc (suc (suc zero))
lookupStateCountExact n bits
  rewrite NatP.*-identityˡ (suc n) = refl

bitCountStrictlyBelowLookupStateCount :
  (n : Nat) →
  (bits : Fin.Fin n → Bool) →
  n < Coded.stateCount (Lookup.lookupCode n bits)
bitCountStrictlyBelowLookupStateCount n bits
  rewrite lookupStateCountExact n bits =
  NatP.<-≤-trans
    (NatP.n<1+n n)
    (NatP.m≤m+n
      (suc n)
      (suc (suc (suc zero))))

descriptionStateCountBelowCookBitCount :
  (description : Description.GuardedCookFormulaDescription) →
  Coded.stateCount (Description.code description)
  ≤ Table.cookBitCount description
descriptionStateCountBelowCookBitCount description =
  transportLeft
    (codedStateWidthExact (Description.code description))
    (StateLower.stateWidthBelowGuardedCookBitCode
      (Coded.codedStateCoverage (Description.code description))
      (Coded.codedSymbolCoverage (Description.code description))
      (Description.nonemptyRules description)
      (Description.input description)
      (Description.steps description))
  where
    transportLeft :
      ∀ {a b c : Nat} → a ≡ b → a ≤ c → b ≤ c
    transportLeft refl proof = proof

tableBakedGeneratorCannotBeDescriptionCode :
  (description : Description.GuardedCookFormulaDescription) →
  Table.fixedCookLookupCode description ≡ Description.code description →
  ⊥
tableBakedGeneratorCannotBeDescriptionCode description sameCode =
  NatP.<-irrefl
    (Table.cookBitCount description)
    (NatP.<-≤-trans
      (bitCountStrictlyBelowLookupStateCount
        (Table.cookBitCount description)
        (Table.cookBitAt description))
      lookupStateCountBelowBitCount)
  where
    lookupStateCountBelowBitCount :
      Coded.stateCount (Table.fixedCookLookupCode description)
      ≤ Table.cookBitCount description
    lookupStateCountBelowBitCount =
      transportCode
        sameCode
        (descriptionStateCountBelowCookBitCount description)

    transportCode :
      ∀ {left right : Coded.CodedFiniteStandardTM} →
      left ≡ right →
      Coded.stateCount right ≤ Table.cookBitCount description →
      Coded.stateCount left ≤ Table.cookBitCount description
    transportCode refl proof = proof

noFixedTableGeneratorBoundary :
  (description : Description.GuardedCookFormulaDescription) →
  Table.FixedTableGeneratorBoundary description →
  ⊥
noFixedTableGeneratorBoundary description boundary =
  tableBakedGeneratorCannotBeDescriptionCode
    description
    (trans
      (sym (Table.generatedCodeExact boundary))
      (Table.sameObjectCode boundary))

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Full bit-table baking is a same-object dead end.  The live generator must use
-- a compact streamed representation: one control state per output bit makes the
-- machine's own one-hot state width larger than the quotation being generated.
------------------------------------------------------------------------
