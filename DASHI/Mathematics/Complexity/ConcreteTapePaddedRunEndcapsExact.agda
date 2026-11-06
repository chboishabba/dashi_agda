module DASHI.Mathematics.Complexity.ConcreteTapePaddedRunEndcapsExact where

------------------------------------------------------------------------
-- EXISTING HEAD MARGINS -> PLAIN PHYSICAL ENDCAPS IN EVERY GENUINE RUN.
--
-- This is the semantic half of guarded SAT completeness. It uses the
-- ORIGINAL WellFormedTapeRun and the ORIGINAL HeadMargin transition
-- theorem, not a newly assumed boundary oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run

-- Nonempty plain suffixes have plain last elements.
endPlainOfNonemptyPlainCells :
  ∀ {State Symbol : Set} {symbol}
    {rest : Agda.Builtin.List.List (Local.TapeCell State Symbol)} →
  WF.PlainCells (Local.plain symbol Agda.Builtin.List.∷ rest) →
  Pattern.EndPlain (Local.plain symbol Agda.Builtin.List.∷ rest)
endPlainOfNonemptyPlainCells (WF.plainCons WF.plainNil) =
  Pattern.endOne
endPlainOfNonemptyPlainCells
    (WF.plainCons (WF.plainCons remaining)) =
  Pattern.endMore
    (endPlainOfNonemptyPlainCells (WF.plainCons remaining))

frontPlainFromOneHeadMargin :
  ∀ {State Symbol : Set}
    {cells : Agda.Builtin.List.List (Local.TapeCell State Symbol)} →
  WF.ExactlyOneHead cells →
  Margin.HeadMargin 1 cells →
  Pattern.FrontPlain cells
frontPlainFromOneHeadMargin (WF.headHere suffixPlain) margin
    with Margin.leftMargin margin
... | ()
frontPlainFromOneHeadMargin (WF.plainBefore tailUnique) margin =
  Pattern.frontCons

endPlainFromOneHeadRightMargin :
  ∀ {State Symbol : Set}
    {cells : Agda.Builtin.List.List (Local.TapeCell State Symbol)} →
  WF.ExactlyOneHead cells →
  suc zero Margin.≤ Margin.rightOfHead cells →
  Pattern.EndPlain cells
endPlainFromOneHeadRightMargin
    (WF.headHere WF.plainNil) ()
endPlainFromOneHeadRightMargin
    (WF.headHere (WF.plainCons plainTail)) rightMargin =
  Pattern.endMore
    (endPlainOfNonemptyPlainCells (WF.plainCons plainTail))
endPlainFromOneHeadRightMargin
    (WF.plainBefore (WF.headHere plainTail)) rightMargin =
  Pattern.endMore
    (endPlainFromOneHeadRightMargin
      (WF.headHere plainTail) rightMargin)
endPlainFromOneHeadRightMargin
    (WF.plainBefore (WF.plainBefore later)) rightMargin =
  Pattern.endMore
    (endPlainFromOneHeadRightMargin
      (WF.plainBefore later) rightMargin)

oneHeadMarginEndcaps :
  ∀ {State Symbol : Set}
    {cells : Agda.Builtin.List.List (Local.TapeCell State Symbol)} →
  WF.ExactlyOneHead cells →
  Margin.HeadMargin 1 cells →
  Pattern.FrontPlain cells × Pattern.EndPlain cells
oneHeadMarginEndcaps unique margin =
  frontPlainFromOneHeadMargin unique margin ,
  endPlainFromOneHeadRightMargin unique (Margin.rightMargin margin)

marginToOne :
  ∀ {State Symbol : Set} {k : Nat}
    {cells : Agda.Builtin.List.List (Local.TapeCell State Symbol)} →
  Margin.HeadMargin (suc k) cells →
  Margin.HeadMargin 1 cells
marginToOne {k = zero} margin = margin
marginToOne {k = suc k} margin =
  marginToOne (Margin.weakenMargin margin)

-- A proof-relevant endcap certificate for every ORIGINAL row in
-- the original accepting-run witness, including the final row.
data AllWellFormedRunRowEndcaps
    {machine : Local.ConcreteTapeMachine} :
    ∀ {start rows finish} →
    Run.WellFormedTapeRun machine start rows finish → Set where

  endcapsDone :
    ∀ {start} →
    (Pattern.FrontPlain (Local.cells start)
     × Pattern.EndPlain (Local.cells start)) →
    AllWellFormedRunRowEndcaps (Run.runDone {row = start})

  endcapsStep :
    ∀ {start next tail finish}
      {step : WF.WellFormedMachineStep machine start next}
      {rest : Run.WellFormedTapeRun machine next tail finish} →
    (Pattern.FrontPlain (Local.cells start)
     × Pattern.EndPlain (Local.cells start)) →
    AllWellFormedRunRowEndcaps rest →
    AllWellFormedRunRowEndcaps (Run.runStep step rest)

allPaddedRunRowsHavePlainEndcaps :
  ∀ {machine start rows finish}
    (run : Run.WellFormedTapeRun machine start rows finish) →
  WF.ExactlyOneHead (Local.cells start) →
  Margin.HeadMargin (suc (Run.runLength run)) (Local.cells start) →
  AllWellFormedRunRowEndcaps run
allPaddedRunRowsHavePlainEndcaps
    Run.runDone unique margin =
  endcapsDone (oneHeadMarginEndcaps unique margin)
allPaddedRunRowsHavePlainEndcaps
    (Run.runStep step rest) unique margin =
  endcapsStep
    (oneHeadMarginEndcaps unique (marginToOne margin))
    (allPaddedRunRowsHavePlainEndcaps
      rest
      (WF.afterExactlyOneHead step)
      (Margin.wellFormedStepMargin step margin))
