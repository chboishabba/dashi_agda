module DASHI.Mathematics.Complexity.CodedFiniteUnaryDelimiterScannerRunExact where

------------------------------------------------------------------------
-- EXACT n+1-STEP RUN FOR THE CONSTANT-CONTROL UNARY DELIMITER SCANNER
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Maybe using (just)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteUnaryDelimiterScannerExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

unaryPayload : Nat → List (Fin.Fin Scan.symbolCount)
unaryPayload zero = Scan.falseTerminator ∷ []
unaryPayload (suc n) = Scan.trueSymbol ∷ unaryPayload n

record SplitUnary (n : Nat) : Set where
  constructor split-unary
  field
    scanned : Fin.Fin Scan.symbolCount
    right : List (Fin.Fin Scan.symbolCount)
    exact : unaryPayload n ≡ scanned ∷ right

splitUnary : (n : Nat) → SplitUnary n
splitUnary zero = split-unary Scan.falseTerminator [] refl
splitUnary (suc n) = split-unary Scan.trueSymbol (unaryPayload n) refl

start : (n : Nat) → Standard.StandardConfiguration Scan.scannerMachine
start n with splitUnary n
... | split-unary scanned right exact =
  Standard.standard-configuration [] Scan.scanState scanned right

finish :
  List (Fin.Fin Scan.symbolCount) →
  Standard.StandardConfiguration Scan.scannerMachine
finish left =
  Standard.standard-configuration left Scan.doneState Scan.falseTerminator []

prependTrues :
  Nat → List (Fin.Fin Scan.symbolCount) → List (Fin.Fin Scan.symbolCount)
prependTrues zero xs = xs
prependTrues (suc k) xs = prependTrues k (Scan.trueSymbol ∷ xs)

scanFrom :
  (n : Nat) → List (Fin.Fin Scan.symbolCount) →
  Standard.StandardConfiguration Scan.scannerMachine
scanFrom zero left =
  Standard.standard-configuration left Scan.scanState Scan.falseTerminator []
scanFrom (suc n) left =
  Standard.standard-configuration
    left Scan.scanState Scan.trueSymbol (unaryPayload n)

scanFromRun :
  (n : Nat)
  (left : List (Fin.Fin Scan.symbolCount)) →
  Run.StandardExactRun
    Scan.scannerMachine
    (suc n)
    (scanFrom n left)
    (finish (prependTrues n left))
scanFromRun zero left =
  Run.standardRunStep edge Run.standardRunDone
  where
    edge :
      Standard.standardNext Scan.scannerMachine (scanFrom zero left)
      ≡ just (finish left)
    edge rewrite Scan.finishFalseTransition = refl
scanFromRun (suc n) left =
  Run.standardRunStep firstEdge (scanFromRun n (Scan.trueSymbol ∷ left))
  where
    firstEdge :
      Standard.standardNext Scan.scannerMachine (scanFrom (suc n) left)
      ≡ just (scanFrom n (Scan.trueSymbol ∷ left))
    firstEdge rewrite Scan.scanTrueTransition = refl

startIsScanFrom : (n : Nat) → start n ≡ scanFrom n []
startIsScanFrom zero = refl
startIsScanFrom (suc n) = refl

unaryDelimiterRunExact :
  (n : Nat) →
  Run.StandardExactRun
    Scan.scannerMachine
    (suc n)
    (start n)
    (finish (prependTrues n []))
unaryDelimiterRunExact n
  rewrite startIsScanFrom n = scanFromRun n []

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Parsing unary value n has exact literal cost n+1 on a constant-size machine.
------------------------------------------------------------------------
