module DASHI.Mathematics.Complexity.GuardedCookStaticBitTableExact where

------------------------------------------------------------------------
-- SAME GUARDED-COOK FORMULA -> LITERAL STATIC FINITE BIT TABLE
--
-- The fixed-description route does not need a runtime higher-order evaluator
-- once the final `(machine,input,T)` description is fixed.  Its exact guarded
-- Cook formula already has a literal finite binary serialization.
--
-- This owner:
--   1. proves that serialization is nonempty by constructor inspection;
--   2. turns the exact head/tail list into a total finite table;
--   3. instantiates CodedFiniteStaticBitLookupExact with that SAME table;
--   4. proves every in-range finite table query equals the existing canonical
--      `GuardedCookBitQuerySemanticsExact.queryAnswer` on the SAME description.
--
-- No external theorem, IIT quantity, semantic oracle, or alternate formula is
-- introduced.  The remaining generator payment is operational: prove the
-- unary-cursor + stop/output finite machine executes the corresponding lookup
-- run with its exact step count.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Canonical
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStaticBitLookupExact as Static

------------------------------------------------------------------------
-- 1. Every exact BooleanFormula binary encoding is nonempty.
------------------------------------------------------------------------

record NonemptyBits (bits : List Bool) : Set where
  constructor nonempty-bits
  field
    head : Bool
    tail : List Bool
    shape : bits ≡ head ∷ tail

open NonemptyBits public

formulaBitsShape :
  (formula : Cook.BooleanFormula) →
  NonemptyBits (Binary.encodeFormulaBits formula)
formulaBitsShape (Cook.variable index) =
  nonempty-bits false
    (true ∷ false ∷ Binary.encodeTokenStream (Prefix.encodeNatInto index []))
    refl
formulaBitsShape (Cook.constant false) =
  nonempty-bits false (true ∷ true ∷ []) refl
formulaBitsShape (Cook.constant true) =
  nonempty-bits true (false ∷ false ∷ []) refl
formulaBitsShape (Cook.negate formula) =
  nonempty-bits true
    (false ∷ true ∷ Binary.encodeFormulaBits formula)
    refl
formulaBitsShape (Cook.conjunction left right) =
  nonempty-bits true
    (true ∷ false ∷ Binary.append
      (Binary.encodeFormulaBits left)
      (Binary.encodeFormulaBits right))
    refl
formulaBitsShape (Cook.disjunction left right) =
  nonempty-bits true
    (true ∷ true ∷ Binary.append
      (Binary.encodeFormulaBits left)
      (Binary.encodeFormulaBits right))
    refl

------------------------------------------------------------------------
-- 2. Exact finite table over a nonempty list.
------------------------------------------------------------------------

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

lookupFin :
  (first : Bool) →
  (rest : List Bool) →
  Fin.Fin (suc (listLength rest)) →
  Bool
lookupFin first rest Fin.zero = first
lookupFin first [] (Fin.suc ())
lookupFin first (next ∷ rest) (Fin.suc index) =
  lookupFin next rest index

finToNat :
  ∀ {n : Nat} →
  Fin.Fin n → Nat
finToNat {suc n} Fin.zero = zero
finToNat {suc n} (Fin.suc index) = suc (finToNat index)

lookupFinMatchesLookupBit :
  (first : Bool) →
  (rest : List Bool) →
  (index : Fin.Fin (suc (listLength rest))) →
  Canonical.lookupBit (finToNat index) (first ∷ rest)
  ≡ just (lookupFin first rest index)
lookupFinMatchesLookupBit first rest Fin.zero = refl
lookupFinMatchesLookupBit first [] (Fin.suc ())
lookupFinMatchesLookupBit first (next ∷ rest) (Fin.suc index) =
  lookupFinMatchesLookupBit next rest index

------------------------------------------------------------------------
-- 3. Formula-native table and literal finite lookup code.
------------------------------------------------------------------------

formulaTail : Cook.BooleanFormula → List Bool
formulaTail formula = tail (formulaBitsShape formula)

formulaHead : Cook.BooleanFormula → Bool
formulaHead formula = head (formulaBitsShape formula)

formulaTable :
  (formula : Cook.BooleanFormula) →
  Fin.Fin (suc (listLength (formulaTail formula))) →
  Bool
formulaTable formula =
  lookupFin (formulaHead formula) (formulaTail formula)

formulaStaticLookupCode :
  (formula : Cook.BooleanFormula) →
  Coded.CodedFiniteStandardTM
formulaStaticLookupCode formula =
  Static.staticLookupCode (formulaTable formula)

formulaTableLookupExact :
  (formula : Cook.BooleanFormula) →
  (index : Fin.Fin (suc (listLength (formulaTail formula)))) →
  Canonical.lookupBit
    (finToNat index)
    (Binary.encodeFormulaBits formula)
  ≡ just (formulaTable formula index)
formulaTableLookupExact formula index
  rewrite shape (formulaBitsShape formula) =
  lookupFinMatchesLookupBit
    (formulaHead formula)
    (formulaTail formula)
    index

------------------------------------------------------------------------
-- 4. SAME guarded-Cook description semantic weld.
------------------------------------------------------------------------

descriptionQueryAnswerAtFiniteIndexExact :
  (description : Description.GuardedCookFormulaDescription) →
  (index : Fin.Fin
    (suc (listLength
      (formulaTail (Description.formula description))))) →
  Semantics.queryAnswer
    (Description.atIndex description (finToNat index))
  ≡ just
      (formulaTable (Description.formula description) index)
descriptionQueryAnswerAtFiniteIndexExact description index =
  formulaTableLookupExact
    (Description.formula description)
    index

------------------------------------------------------------------------
-- 5. Max-cut / attribution boundary.
------------------------------------------------------------------------

record GuardedCookStaticBitTableBoundary : Set where
  constructor guarded-cook-static-bit-table-boundary
  field
    exactFormulaSerializationUsed : Bool
    serializationProvedNonempty : Bool
    finiteStaticAnswerTableConstructed : Bool
    literalFiniteLookupCodeConstructed : Bool
    sameDescriptionQuerySemanticsMatched : Bool
    runtimeHigherOrderPredicateRequired : Bool
    alternateFormulaOrOracleIntroduced : Bool
    exactMachineLookupRunStillRequired : Bool

open GuardedCookStaticBitTableBoundary public

canonicalGuardedCookStaticBitTableBoundary :
  GuardedCookStaticBitTableBoundary
canonicalGuardedCookStaticBitTableBoundary =
  guarded-cook-static-bit-table-boundary
    true true true true true false false true

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The fixed-description generator's complete answer table is now sourced from
-- the SAME guarded Cook formula consumed by the diagonal.  For every in-range
-- finite index, the precompiled table bit is propositionally identical to the
-- already-authoritative canonical queryAnswer.  The only generator seam left
-- here is operational execution of the literal unary cursor + stop/output rule,
-- not semantic table population.
------------------------------------------------------------------------
