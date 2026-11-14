module DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact where

------------------------------------------------------------------------
-- SET-LEVEL CODED POLYNOMIAL DECIDER WITNESS
--
-- IMPORTANT RESOURCE FIREWALL
--
-- The execution clock is NOT an arbitrary Formula -> Nat field. The guarded
-- finite simulation itself depends on T, so such a field could become an input
-- side-channel. The concrete model instead runs for the canonical size-only
-- arithmetic clock over the ACTUAL serialized input length:
--
--   T(phi) = c * (1 + formulaBitCodeLength(phi))^d.
--
-- The two input bit symbols are distinct from each other AND from blank, and
-- the symbol-list length is proved exactly equal to formulaBitCodeLength.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as ClockArithmetic

mapFormulaBits :
  ∀ {n : Nat} →
  Fin.Fin n →
  Fin.Fin n →
  List Bool →
  List (Fin.Fin n)
mapFormulaBits zeroSymbol oneSymbol [] = []
mapFormulaBits zeroSymbol oneSymbol (false ∷ bits) =
  zeroSymbol ∷ mapFormulaBits zeroSymbol oneSymbol bits
mapFormulaBits zeroSymbol oneSymbol (true ∷ bits) =
  oneSymbol ∷ mapFormulaBits zeroSymbol oneSymbol bits

mapFormulaBitsLength :
  ∀ {n : Nat}
    (zeroSymbol oneSymbol : Fin.Fin n)
    (bits : List Bool) →
  Binary.listLength (mapFormulaBits zeroSymbol oneSymbol bits)
  ≡ Binary.listLength bits
mapFormulaBitsLength zeroSymbol oneSymbol [] = refl
mapFormulaBitsLength zeroSymbol oneSymbol (false ∷ bits)
    rewrite mapFormulaBitsLength zeroSymbol oneSymbol bits = refl
mapFormulaBitsLength zeroSymbol oneSymbol (true ∷ bits)
    rewrite mapFormulaBitsLength zeroSymbol oneSymbol bits = refl

formulaInput :
  (code : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.symbolCount code) →
  Fin.Fin (Coded.symbolCount code) →
  Cook.BooleanFormula →
  List (Fin.Fin (Coded.symbolCount code))
formulaInput code zeroSymbol oneSymbol formula =
  mapFormulaBits zeroSymbol oneSymbol
    (Binary.encodeFormulaBits formula)

formulaInputLengthExact :
  (code : Coded.CodedFiniteStandardTM)
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount code))
  (formula : Cook.BooleanFormula) →
  Binary.listLength (formulaInput code zeroSymbol oneSymbol formula)
  ≡ Binary.formulaBitCodeLength formula
formulaInputLengthExact code zeroSymbol oneSymbol formula =
  mapFormulaBitsLength
    zeroSymbol oneSymbol (Binary.encodeFormulaBits formula)

polynomialStepBudget :
  Nat → Nat → Cook.BooleanFormula → Nat
polynomialStepBudget = ClockArithmetic.formulaPolynomialBudget

record CodedStandardPolynomialDecider
    (decider : Cook.BooleanFormula → Bool) : Set where
  field
    code : Coded.CodedFiniteStandardTM

    zeroSymbol : Fin.Fin (Coded.symbolCount code)
    oneSymbol : Fin.Fin (Coded.symbolCount code)
    binarySymbolsDistinct : zeroSymbol ≡ oneSymbol → ⊥
    zeroSymbolNotBlank : zeroSymbol ≡ Coded.blank code → ⊥
    oneSymbolNotBlank : oneSymbol ≡ Coded.blank code → ⊥

    clockCoefficient : Nat
    clockDegree : Nat

    finish :
      (formula : Cook.BooleanFormula) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM code))

    execution :
      (formula : Cook.BooleanFormula) →
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine
          (Coded.decodeCodedStandardTM code))
        (polynomialStepBudget clockCoefficient clockDegree formula)
        (Language.guardedStandardStart
          (formulaInput code zeroSymbol oneSymbol formula)
          (polynomialStepBudget clockCoefficient clockDegree formula))
        (finish formula)

    decisionExact :
      (formula : Cook.BooleanFormula) →
      Coded.finEqual
        (Standard.state (finish formula))
        (Coded.acceptingState code)
      ≡ decider formula

open CodedStandardPolynomialDecider public

record CodedStandardPolynomialDeciderBoundary : Set where
  constructor coded-standard-polynomial-decider-boundary
  field
    finiteProgramCodeInSet : Bool
    faithfulBinaryInputSymbols : Bool
    binarySymbolsSeparatedFromBlank : Bool
    literalInputLengthCharged : Bool
    canonicalSizeOnlyPolynomialClock : Bool
    exactStandardRunCarried : Bool
    finalDecisionExact : Bool
    arbitraryFormulaDependentClockAllowed : Bool
    mapPrecompositionClosurePaid : Bool
    verifierClosurePaid : Bool

canonicalCodedStandardPolynomialDeciderBoundary :
  CodedStandardPolynomialDeciderBoundary
canonicalCodedStandardPolynomialDeciderBoundary =
  coded-standard-polynomial-decider-boundary
    true true true true true true true false false false

------------------------------------------------------------------------
-- FRONTIER
--
-- `polynomialTimeDecider = CodedStandardPolynomialDecider` is a machine-bearing
-- Set-level predicate with faithful nonblank binary input and a clock polynomial
-- in the exact literal input length. No hidden extensional timing oracle remains.
------------------------------------------------------------------------
