module DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact where

------------------------------------------------------------------------
-- LOW-UNIVERSE CODED FINITE STANDARD TURING MACHINE
--
-- PolynomialCostModel.polynomialTimeDecider returns a witness in `Set`.  The
-- existing universe-polymorphic `FinitePresentedStandardTM` is the right
-- semantic machine carrier but is too large to serve directly as such a code.
--
-- This owner supplies a literal `Set`-level program representation:
--
--   states  = Fin stateCount
--   symbols = Fin symbolCount
--   program = blank/initial/accepting indices + finite rule list.
--
-- The ordinary finite enumerations and genuine EnumerationCoverage witnesses
-- are constructed from the cardinalities, then the code is decoded into the
-- existing FinitePresentedStandardTM *without changing the rule table*.
--
-- No claim is made that the old abstract PolynomialCostModel supplies this code.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented

------------------------------------------------------------------------
-- Canonical Fin enumeration.
------------------------------------------------------------------------

mapFinSuc :
  ∀ {n : Nat} →
  List (Fin.Fin n) →
  List (Fin.Fin (suc n))
mapFinSuc [] = []
mapFinSuc (x ∷ xs) = Fin.suc x ∷ mapFinSuc xs

allFin :
  (n : Nat) →
  List (Fin.Fin n)
allFin zero = []
allFin (suc n) = Fin.zero ∷ mapFinSuc (allFin n)

finEqual :
  ∀ {n : Nat} →
  Fin.Fin n →
  Fin.Fin n →
  Bool
finEqual {suc n} Fin.zero Fin.zero = true
finEqual {suc n} Fin.zero (Fin.suc y) = false
finEqual {suc n} (Fin.suc x) Fin.zero = false
finEqual {suc n} (Fin.suc x) (Fin.suc y) = finEqual x y

finEqualRefl :
  ∀ {n : Nat} →
  (x : Fin.Fin n) →
  finEqual x x ≡ true
finEqualRefl {suc n} Fin.zero = refl
finEqualRefl {suc n} (Fin.suc x) = finEqualRefl x

finEqualSound :
  ∀ {n : Nat} {x y : Fin.Fin n} →
  finEqual x y ≡ true →
  x ≡ y
finEqualSound {suc n} {Fin.zero} {Fin.zero} proof = refl
finEqualSound {suc n} {Fin.zero} {Fin.suc y} ()
finEqualSound {suc n} {Fin.suc x} {Fin.zero} ()
finEqualSound {suc n} {Fin.suc x} {Fin.suc y} proof
    with finEqualSound {x = x} {y = y} proof
... | refl = refl

canonicalFinEnumeration :
  (n : Nat) →
  Local.FiniteEnumeration (Fin.Fin n)
canonicalFinEnumeration n = record
  { Local.values = allFin n
  ; Local.occurs = λ x → ⊤
  ; Local.complete = λ x → tt
  ; Local.decideEqual = finEqual
  ; Local.decideEqualRefl = finEqualRefl
  ; Local.decideEqualSound = finEqualSound
  }

------------------------------------------------------------------------
-- Genuine list-membership coverage for `allFin`.
------------------------------------------------------------------------

mapSucMember :
  ∀ {n : Nat} {x : Fin.Fin n} {xs : List (Fin.Fin n)} →
  Canonical.Member x xs →
  Canonical.Member (Fin.suc x) (mapFinSuc xs)
mapSucMember Canonical.here = Canonical.here
mapSucMember (Canonical.there member) =
  Canonical.there (mapSucMember member)

allFinMember :
  ∀ {n : Nat} →
  (x : Fin.Fin n) →
  Canonical.Member x (allFin n)
allFinMember {suc n} Fin.zero = Canonical.here
allFinMember {suc n} (Fin.suc x) =
  Canonical.there (mapSucMember (allFinMember x))

canonicalFinCoverage :
  (n : Nat) →
  Canonical.EnumerationCoverage (canonicalFinEnumeration n)
canonicalFinCoverage n = record
  { Canonical.listed = allFinMember }

------------------------------------------------------------------------
-- Set-level finite program text.
------------------------------------------------------------------------

record CodedFiniteStandardTM : Set where
  field
    stateCount : Nat
    symbolCount : Nat

    blank : Fin.Fin symbolCount
    initialState : Fin.Fin stateCount
    acceptingState : Fin.Fin stateCount

    rules :
      List
        (Local.TapeRule
          (Fin.Fin stateCount)
          (Fin.Fin symbolCount))

    dispatchUnique :
      ∀ {left right :
          Local.TapeRule
            (Fin.Fin stateCount)
            (Fin.Fin symbolCount)} →
      Local.RuleOccurs left rules →
      Local.RuleOccurs right rules →
      Local.sourceState left ≡ Local.sourceState right →
      Local.readSymbol left ≡ Local.readSymbol right →
      left ≡ right

open CodedFiniteStandardTM public

------------------------------------------------------------------------
-- Decode into the already-established standard finite presentation.
------------------------------------------------------------------------

decodeCodedStandardTM :
  CodedFiniteStandardTM →
  Presented.FinitePresentedStandardTM
decodeCodedStandardTM code = record
  { Presented.State = Fin.Fin (stateCount code)
  ; Presented.Symbol = Fin.Fin (symbolCount code)
  ; Presented.finiteState = canonicalFinEnumeration (stateCount code)
  ; Presented.finiteSymbol = canonicalFinEnumeration (symbolCount code)
  ; Presented.blank = blank code
  ; Presented.initialState = initialState code
  ; Presented.acceptingState = acceptingState code
  ; Presented.rules = rules code
  ; Presented.dispatchUnique = dispatchUnique code
  }

codedStateCoverage :
  (code : CodedFiniteStandardTM) →
  Canonical.EnumerationCoverage
    (Presented.finiteState (decodeCodedStandardTM code))
codedStateCoverage code =
  canonicalFinCoverage (stateCount code)

codedSymbolCoverage :
  (code : CodedFiniteStandardTM) →
  Canonical.EnumerationCoverage
    (Presented.finiteSymbol (decodeCodedStandardTM code))
codedSymbolCoverage code =
  canonicalFinCoverage (symbolCount code)

------------------------------------------------------------------------
-- Exact program-data preservation.
------------------------------------------------------------------------

codedRulesExact :
  (code : CodedFiniteStandardTM) →
  Presented.rules (decodeCodedStandardTM code) ≡ rules code
codedRulesExact code = refl

codedBlankExact :
  (code : CodedFiniteStandardTM) →
  Presented.blank (decodeCodedStandardTM code) ≡ blank code
codedBlankExact code = refl

codedInitialExact :
  (code : CodedFiniteStandardTM) →
  Presented.initialState (decodeCodedStandardTM code) ≡ initialState code
codedInitialExact code = refl

codedAcceptingExact :
  (code : CodedFiniteStandardTM) →
  Presented.acceptingState (decodeCodedStandardTM code) ≡ acceptingState code
codedAcceptingExact code = refl

------------------------------------------------------------------------
-- FRONTIER
--
-- The repository now has a genuine `Set`-level standard-machine program code,
-- suitable in principle for a machine-bearing PolynomialCostModel predicate.
-- What is NOT yet paid is the universal interpreter/evaluator layer that maps
-- such a code plus a serialized BooleanFormula input to its bounded execution.
-- That evaluator is the remaining representation ingredient needed to define
-- a fully concrete standard-machine cost model inside `PolynomialCostModel`.
------------------------------------------------------------------------
