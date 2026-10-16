module DASHI.Mathematics.Complexity.PNotEqualsNPKleeneUniversalQuotedInputFidelityExact where

------------------------------------------------------------------------
-- CANONICAL UNIVERSAL INPUT = TYPED p-ON-q INPUT AFTER Fin->Nat ERASURE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterFidelityExact as Fidelity
import DASHI.Mathematics.Complexity.CodedFiniteStandardUniversalQuotedInputExact as Universal
import DASHI.Mathematics.Complexity.CodedStandardCanonicalInputExact as CanonicalInput
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneQuotedBodyCookDescriptionExact as Quoted
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

mapBoolNatExact :
  ∀ {n : Nat}
    (zeroSymbol oneSymbol : Fin.Fin n)
    (bits : List Bool) →
  Universal.mapBoolNat
    (Fin.toℕ zeroSymbol)
    (Fin.toℕ oneSymbol)
    bits
  ≡
  Fidelity.finListToNat
    (Query.mapBoolSymbols zeroSymbol oneSymbol bits)
mapBoolNatExact zeroSymbol oneSymbol [] = refl
mapBoolNatExact zeroSymbol oneSymbol (false ∷ rest)
  rewrite mapBoolNatExact zeroSymbol oneSymbol rest = refl
mapBoolNatExact zeroSymbol oneSymbol (true ∷ rest)
  rewrite mapBoolNatExact zeroSymbol oneSymbol rest = refl

rawQuotedStartExact :
  (body : Coded.CodedFiniteStandardTM)
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body))
  (bits : List Bool) →
  Universal.rawStartOnQuote
    (DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact.rawMachineView body)
    (Fin.toℕ zeroSymbol)
    (Fin.toℕ oneSymbol)
    bits
  ≡
  Fidelity.rawConfigurationOf
    (CanonicalInput.canonicalStandardStart
      {machine = Fidelity.codedConcrete body}
      (Query.mapBoolSymbols zeroSymbol oneSymbol bits))
rawQuotedStartExact body zeroSymbol oneSymbol [] = refl
rawQuotedStartExact body zeroSymbol oneSymbol (false ∷ rest)
  rewrite mapBoolNatExact zeroSymbol oneSymbol rest = refl
rawQuotedStartExact body zeroSymbol oneSymbol (true ∷ rest)
  rewrite mapBoolNatExact zeroSymbol oneSymbol rest = refl

canonicalUniversalInputFollowsTypedRun :
  (body : Coded.CodedFiniteStandardTM)
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body))
  ∀ {steps : Nat}
    {finish : Standard.StandardConfiguration (Fidelity.codedStandard body)} →
  Run.StandardExactRun
    (Fidelity.codedStandard body)
    steps
    (CanonicalInput.canonicalStandardStart
      {machine = Fidelity.codedConcrete body}
      (Quoted.fixedPointQuoteInput body zeroSymbol oneSymbol))
    finish →
  Universal.runCanonicalUniversalQuotedInput
    steps body zeroSymbol oneSymbol
  ≡ just (Fidelity.rawConfigurationOf finish)
canonicalUniversalInputFollowsTypedRun body zeroSymbol oneSymbol run
  rewrite rawQuotedStartExact
    body zeroSymbol oneSymbol (Quoted.fixedPointQuoteBits body) =
  Fidelity.rawIterateFollowsStandardRun body run

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The single canonical universal input and the typed p-on-q computation are now
-- literally the same simulated run after the explicit Fin->Nat erasure.  A
-- standard-TM implementation U of the raw interpreter therefore needs no extra
-- semantic adapter between its decoded input and the Clay-facing body run.
------------------------------------------------------------------------
