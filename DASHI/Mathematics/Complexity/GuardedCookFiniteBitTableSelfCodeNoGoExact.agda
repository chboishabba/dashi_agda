module DASHI.Mathematics.Complexity.GuardedCookFiniteBitTableSelfCodeNoGoExact where

------------------------------------------------------------------------
-- FULL-TABLE-BAKED OWN-COOK GENERATOR CANNOT BE ITS OWN DESCRIBED MACHINE
--
-- Let n be the binary length of the fixed guarded Cook formula.  The literal
-- lookup compiler needs n+1 cursor controls plus three output sinks, so its
-- coded state count is strictly greater than n.  But every guarded Cook binary
-- quotation is at least the one-hot StateWidth of the very machine it describes.
-- If the generated lookup code were literally the description code, this would
-- force
--
--   n < stateCount(lookup) <= n,
--
-- a contradiction.
--
-- Thus the table-baked baseline is a real finite generator for a FIXED external
-- description, but it cannot close the same-object own-code equation.  The live
-- self-reference route must retain compact/streamed generation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookFiniteBitTableGeneratorExact as Table
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupExact as Lookup
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinStateWidthLowerExact as StateLower

------------------------------------------------------------------------
-- Coded Fin state width is exactly the declared state cardinality.
------------------------------------------------------------------------

mapFinSucLength :
  ∀ {n : Nat} (xs : Agda.Builtin.List.List (Data.Fin.Base.Fin n)) →
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

------------------------------------------------------------------------
-- The table lookup compiler has strictly more controls than table bits.
------------------------------------------------------------------------

lookupStateCountExact :
  (n : Nat) →
  (bits : Data.Fin.Base.Fin n → Agda.Builtin.Bool.Bool) →
  Coded.stateCount (Lookup.lookupCode n bits)
  ≡ suc n + suc (suc (suc zero))
lookupStateCountExact n bits = refl

bitCountStrictlyBelowLookupStateCount :
  (n : Nat) →
  (bits : Data.Fin.Base.Fin n → Agda.Builtin.Bool.Bool) →
  n < Coded.stateCount (Lookup.lookupCode n bits)
bitCountStrictlyBelowLookupStateCount n bits
  rewrite lookupStateCountExact n bits =
  NatP.<-≤-trans
    (NatP.n<1+n n)
    (NatP.m≤m+n
      (suc n)
      (suc (suc (suc zero))))

------------------------------------------------------------------------
-- Every fixed description already bounds its coded state count by its own Cook
-- binary quotation length.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Main same-object no-go.
------------------------------------------------------------------------

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
-- Full bit-table baking is now closed as a same-object dead end, not merely
-- deemed inefficient.  The successful fixed-description generator must compute
-- Cook bits from a compact representation whose control/state width does not
-- itself contain one state per output bit.  This validates the branch's streamed
-- clause/token/index architecture as the live route.
------------------------------------------------------------------------
