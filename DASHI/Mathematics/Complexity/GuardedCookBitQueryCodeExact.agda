module DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact where

------------------------------------------------------------------------
-- CANONICAL ANSWER-BLIND QUERY CODE FOR ONE GUARDED COOK FORMULA BIT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as Program
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

bitsToList :
  ∀ {width : Nat} →
  CNF.Bits width → List Bool
bitsToList CNF.[]ᵇ = []
bitsToList (bit CNF.∷ᵇ rest) = bit ∷ bitsToList rest

unaryNat : Nat → List Bool
unaryNat zero = false ∷ []
unaryNat (suc n) = true ∷ unaryNat n

appendMany : List (List Bool) → List Bool
appendMany [] = []
appendMany (section ∷ sections) =
  Local.append section (appendMany sections)

inputSymbolBits :
  (code : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.symbolCount code) →
  List Bool
inputSymbolBits code symbol =
  bitsToList
    (Canonical.encode
      (Canonical.canonicalFiniteCodec
        (Coded.canonicalFinEnumeration (Coded.symbolCount code))
        (Coded.canonicalFinCoverage (Coded.symbolCount code))
        (Coded.blank code))
      symbol)

encodeInputSymbols :
  (code : Coded.CodedFiniteStandardTM) →
  List (Fin.Fin (Coded.symbolCount code)) →
  List Bool
encodeInputSymbols code [] = []
encodeInputSymbols code (symbol ∷ symbols) =
  Local.append
    (inputSymbolBits code symbol)
    (encodeInputSymbols code symbols)

record GuardedCookBitQuery : Set₁ where
  field
    code : Coded.CodedFiniteStandardTM

    nonemptyRules :
      Selector.NonemptyRuleTable
        (Presented.finitePresentedStandardToConcrete
          (Coded.decodeCodedStandardTM code))

    input :
      Input.InputWord
        (Presented.finitePresentedStandardToConcrete
          (Coded.decodeCodedStandardTM code))

    steps : Nat
    index : Nat

open GuardedCookBitQuery public

withIndex :
  GuardedCookBitQuery → Nat → GuardedCookBitQuery
withIndex query newIndex = record
  { code = code query
  ; nonemptyRules = nonemptyRules query
  ; input = input query
  ; steps = steps query
  ; index = newIndex
  }

withIndexFormulaExact :
  (query : GuardedCookBitQuery)
  (newIndex : Nat) →
  queryFormula (withIndex query newIndex)
  ≡ queryFormula query
withIndexFormulaExact query newIndex = refl
  where
    queryFormula : GuardedCookBitQuery → Cook.BooleanFormula
    queryFormula q =
      CookLevin.guardedCookFormula
        (Coded.codedStateCoverage (code q))
        (Coded.codedSymbolCoverage (code q))
        (nonemptyRules q)
        (input q)
        (steps q)

withIndexIndexExact :
  (query : GuardedCookBitQuery)
  (newIndex : Nat) →
  index (withIndex query newIndex) ≡ newIndex
withIndexIndexExact query newIndex = refl

queryMachine :
  GuardedCookBitQuery → Local.ConcreteTapeMachine
queryMachine query =
  Presented.finitePresentedStandardToConcrete
    (Coded.decodeCodedStandardTM (code query))

queryFormula :
  (query : GuardedCookBitQuery) →
  Cook.BooleanFormula
queryFormula query =
  CookLevin.guardedCookFormula
    (Coded.codedStateCoverage (code query))
    (Coded.codedSymbolCoverage (code query))
    (nonemptyRules query)
    (input query)
    (steps query)

queryProgramBits :
  (query : GuardedCookBitQuery) →
  List Bool
queryProgramBits query =
  bitsToList
    (Program.encodeStaticProgram
      (queryMachine query)
      (Coded.codedStateCoverage (code query))
      (Coded.codedSymbolCoverage (code query)))

queryBits :
  GuardedCookBitQuery → List Bool
queryBits query =
  appendMany
    ( unaryNat (Coded.stateCount (code query))
    ∷ unaryNat (Coded.symbolCount (code query))
    ∷ unaryNat (Canonical.listLength (Coded.rules (code query)))
    ∷ queryProgramBits query
    ∷ unaryNat (Canonical.listLength (input query))
    ∷ encodeInputSymbols (code query) (input query)
    ∷ unaryNat (steps query)
    ∷ unaryNat (index query)
    ∷ [] )

queryBitLength : GuardedCookBitQuery → Nat
queryBitLength query = Canonical.listLength (queryBits query)

mapBoolSymbols :
  ∀ {Symbol : Set} →
  Symbol → Symbol → List Bool → List Symbol
mapBoolSymbols zeroSymbol oneSymbol [] = []
mapBoolSymbols zeroSymbol oneSymbol (false ∷ bits) =
  zeroSymbol ∷ mapBoolSymbols zeroSymbol oneSymbol bits
mapBoolSymbols zeroSymbol oneSymbol (true ∷ bits) =
  oneSymbol ∷ mapBoolSymbols zeroSymbol oneSymbol bits

------------------------------------------------------------------------
-- FIREWALL
--
-- `withIndex` changes ONLY the requested position. Machine code, literal input
-- and T are fixed across all reads of one described Cook formula.
------------------------------------------------------------------------
