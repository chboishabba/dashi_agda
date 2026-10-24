module DASHI.Mathematics.Complexity.PNotEqualsNPLiteralCookQuotationSelfInputNoGoExact where

------------------------------------------------------------------------
-- LITERAL COOK-QUOTATION SELF-INPUT NO-GO
--
-- ConcreteTapeCookLevinQuotationGrowthExact already proves that for every
-- nonempty literal tape input:
--
--   payloadLength(input)
--     < bitCodeLength(guardedCookFormula machine input steps).
--
-- This owner promotes the research consequence to exact theorem form:
-- literal equality between the input payload length and the binary encoding of
-- the Cook--Levin formula generated from that same input is impossible.
--
-- Therefore the final self-diagonal construction cannot be a raw source-string
-- quine of the full Cook formula.  It must use an intensional/behavioural fixed
-- point plus a separately proved execution-semantics quotation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinQuotationGrowthExact as Growth
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

------------------------------------------------------------------------
-- A strict inequality forbids exact equality of the two lengths.
------------------------------------------------------------------------

strictBelowForbidsEquality :
  ∀ {left right : Nat} →
  left < right →
  left ≡ right →
  ⊥
strictBelowForbidsEquality strict equality
    rewrite equality =
  irreflexive strict
  where
    irreflexive :
      ∀ {n : Nat} →
      n < n →
      ⊥
    irreflexive ()

------------------------------------------------------------------------
-- Main no-go.
------------------------------------------------------------------------

literalCookQuotationPayloadLengthCannotClose :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (symbol : Local.Symbol machine)
    (rest : List (Local.Symbol machine))
    (steps : Nat) →
  Input.inputPayloadLength (symbol ∷ rest)
  ≡
  Binary.formulaBitCodeLength
    (CookLevin.guardedCookFormula
      stateCoverage
      symbolCoverage
      nonempty
      (symbol ∷ rest)
      steps) →
  ⊥
literalCookQuotationPayloadLengthCannotClose
    stateCoverage
    symbolCoverage
    nonempty
    symbol
    rest
    steps =
  strictBelowForbidsEquality
    (Growth.nonemptyPayloadStrictlyBelowCookFormulaBitCode
      stateCoverage
      symbolCoverage
      nonempty
      symbol
      rest
      steps)

------------------------------------------------------------------------
-- Symmetric presentation: even if an attempted quine states the formula-code
-- length equals the payload length, contradiction follows.
------------------------------------------------------------------------

literalCookQuotationBitCodeLengthCannotEqualPayload :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (symbol : Local.Symbol machine)
    (rest : List (Local.Symbol machine))
    (steps : Nat) →
  Binary.formulaBitCodeLength
    (CookLevin.guardedCookFormula
      stateCoverage
      symbolCoverage
      nonempty
      (symbol ∷ rest)
      steps)
  ≡
  Input.inputPayloadLength (symbol ∷ rest) →
  ⊥
literalCookQuotationBitCodeLengthCannotEqualPayload
    stateCoverage
    symbolCoverage
    nonempty
    symbol
    rest
    steps
    equality =
  literalCookQuotationPayloadLengthCannotClose
    stateCoverage
    symbolCoverage
    nonempty
    symbol
    rest
    steps
    (sym equality)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The concrete full-tableau Cook--Levin constructor cannot literally consume
-- its own complete binary formula quotation as a nonempty symbol-for-bit input.
-- The surviving semantic diagonal must therefore use:
--
--   * finite/intensional self-description at the program level;
--   * a concrete interpreter for that description;
--   * Cook--Levin quotation of the interpreter run;
--   * resource closure without requiring literal source equality.
------------------------------------------------------------------------
