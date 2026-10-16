module DASHI.Mathematics.Complexity.CodedFiniteUnaryDelimiterScannerRunExact where

------------------------------------------------------------------------
-- EXACT n+1-STEP RUN FOR THE CONSTANT-CONTROL UNARY DELIMITER SCANNER
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Maybe using (just)

import DASHI.Mathematics.Complexity.CodedFiniteUnaryDelimiterScannerExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

unaryPayload : Nat → List (Data.Fin.Base.Fin Scan.symbolCount)
unaryPayload zero = Scan.falseTerminator ∷ []
unaryPayload (suc n) = Scan.trueSymbol ∷ unaryPayload n

record SplitUnary (n : Nat) : Set where
  constructor split-unary
  field
    scanned : Data.Fin.Base.Fin Scan.symbolCount
    right : List (Data.Fin.Base.Fin Scan.symbolCount)
    exact : unaryPayload n ≡ scanned ∷ right

splitUnary : (n : Nat) → SplitUnary n
splitUnary zero = split-unary Scan.falseTerminator [] refl
splitUnary (suc n) = split-unary Scan.trueSymbol (unaryPayload n) refl

start :
  (n : Nat) →
  Standard.StandardConfiguration Scan.scannerMachine
start n with splitUnary n
... | split-unary scanned right exact =
  Standard.standard-configuration [] Scan.scanState scanned right

finish :
  (left : List (Data.Fin.Base.Fin Scan.symbolCount)) →
  Standard.StandardConfiguration Scan.scannerMachine
finish left =
  Standard.standard-configuration
    left Scan.doneState Scan.falseTerminator []

------------------------------------------------------------------------
-- More general accumulator theorem: after k payload bits have already been
-- crossed, scanning n remaining true bits plus the terminator takes n+1 edges.
------------------------------------------------------------------------

scanFrom :
  (n : Nat)
  (left : List (Data.Fin.Base.Fin Scan.symbolCount)) →
  Standard.StandardConfiguration Scan.scannerMachine
scanFrom zero left =
  Standard.standard-configuration
    left Scan.scanState Scan.falseTerminator []
scanFrom (suc n) left =
  Standard.standard-configuration
    left Scan.scanState Scan.trueSymbol (unaryPayload n)

scanFinish :
  (n : Nat)
  (left : List (Data.Fin.Base.Fin Scan.symbolCount)) →
  Standard.StandardConfiguration Scan.scannerMachine
scanFinish n left =
  finish (prependTrues n left)
  where
    prependTrues :
      Nat →
      List (Data.Fin.Base.Fin Scan.symbolCount) →
      List (Data.Fin.Base.Fin Scan.symbolCount)
    prependTrues zero xs = xs
    prependTrues (suc k) xs = prependTrues k (Scan.trueSymbol ∷ xs)

prependTrues :
  Nat →
  List (Data.Fin.Base.Fin Scan.symbolCount) →
  List (Data.Fin.Base.Fin Scan.symbolCount)
prependTrues zero xs = xs
prependTrues (suc k) xs = prependTrues k (Scan.trueSymbol ∷ xs)

scanFromRun :
  (n : Nat)
  (left : List (Data.Fin.Base.Fin Scan.symbolCount)) →
  Run.StandardExactRun
    Scan.scannerMachine
    (suc n)
    (scanFrom n left)
    (finish (prependTrues n left))
scanFromRun zero left =
  Run.standardRunStep
    (transitionStep Scan.finishFalseTransition)
    Run.standardRunDone
  where
    transitionStep :
      Standard.transition Scan.scannerMachine Scan.scanState Scan.falseTerminator
      ≡ just
        (Standard.standard-transition
          Scan.doneState Scan.falseTerminator
          DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact.stayPut) →
      Standard.standardNext Scan.scannerMachine (scanFrom zero left)
      ≡ just (finish left)
    transitionStep equality rewrite equality = refl
scanFromRun (suc n) left =
  Run.standardRunStep firstEdge (scanFromRun n (Scan.trueSymbol ∷ left))
  where
    firstEdge :
      Standard.standardNext
        Scan.scannerMachine
        (scanFrom (suc n) left)
      ≡
      just (scanFrom n (Scan.trueSymbol ∷ left))
    firstEdge rewrite Scan.scanTrueTransition = refl

startIsScanFrom :
  (n : Nat) → start n ≡ scanFrom n []
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
-- Parsing one self-delimiting unary natural has exact literal cost n+1 on the
-- constant-size scanner.  No phase expansion or meta-level arithmetic oracle is
-- used; this is an ordinary StandardExactRun of the actual two-state machine.
------------------------------------------------------------------------
