module DASHI.Mathematics.Complexity.ConcreteTapeWholeRowCNFWeldExact where

------------------------------------------------------------------------
-- WHOLE-ROW LOCAL CNF SEMANTICS
--
-- Given any fixed-width codec for six-cell windows, replicate the canonical
-- truth-table CNF over every window emitted by the recursive row scanner.
-- Combined with the already-proved semantic whole-row locality theorem, this
-- yields both directions:
--
--   well-formed machine step
--      -> every local encoded CNF is satisfied
--
-- and, under the same explicit padded/interior-head and fixed-width conditions,
--
--   every local encoded CNF satisfied
--      -> well-formed machine step.
--
-- No concrete Cell/Bits encoding is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Locality
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Weld
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

data AllEncodedWindowCNFSatisfied
    {machine : Local.ConcreteTapeMachine}
    {width : Nat}
    (codec : Weld.FixedWidthWindowCodec machine width)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)) :
    List (Local.SixCellWindow machine) →
    Set where

  allCNFNil :
    AllEncodedWindowCNFSatisfied codec rule []

  allCNFCons :
    ∀ {window windows} →
    CNF.evaluateCNF
      (Weld.encodedWindowCNF codec rule)
      (Weld.encode codec window)
    ≡ true →
    AllEncodedWindowCNFSatisfied codec rule windows →
    AllEncodedWindowCNFSatisfied codec rule
      (window ∷ windows)

semanticAllWindowsToCNF :
  ∀ {machine width rule windows}
    (codec : Weld.FixedWidthWindowCodec machine width) →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    windows →
  AllEncodedWindowCNFSatisfied codec rule windows
semanticAllWindowsToCNF codec Whole.allNil =
  allCNFNil
semanticAllWindowsToCNF codec
    (Whole.allCons legal rest) =
  allCNFCons
    (Weld.semanticLegalImpliesEncodedCNF codec legal)
    (semanticAllWindowsToCNF codec rest)

cnfAllWindowsToSemantic :
  ∀ {machine width rule windows}
    (codec : Weld.FixedWidthWindowCodec machine width) →
  AllEncodedWindowCNFSatisfied codec rule windows →
  Whole.All
    (Pattern.LegalWindowForRule machine rule)
    windows
cnfAllWindowsToSemantic codec allCNFNil =
  Whole.allNil
cnfAllWindowsToSemantic codec
    (allCNFCons cnfTrue rest) =
  Whole.allCons
    (Weld.encodedCNFImpliesSemanticLegal codec cnfTrue)
    (cnfAllWindowsToSemantic codec rest)

stepImpliesWholeRowCNF :
  ∀ {machine width before after}
    (codec : Weld.FixedWidthWindowCodec machine width) →
  (wellFormed : WF.WellFormedMachineStep machine before after) →
  AllEncodedWindowCNFSatisfied
    codec
    (Local.rule (WF.step wellFormed))
    (Whole.scanWindows machine before after)
stepImpliesWholeRowCNF codec wellFormed =
  semanticAllWindowsToCNF codec
    (Whole.machineStepImpliesAllWindowsLegal wellFormed)

record EncodedTransitionCNFCharacterization
    {machine : Local.ConcreteTapeMachine}
    {width : Nat}
    (codec : Weld.FixedWidthWindowCodec machine width)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (before after : Local.TapeRow machine) : Set where
  field
    beforeInterior :
      Locality.InteriorHeadConfiguration machine before

    afterUnique :
      WF.ExactlyOneHead (Local.cells after)

    ruleOccursInMachine :
      Local.RuleOccurs rule (Local.rules machine)

    sameRowLength :
      Coordinate.listLength (Local.cells before)
      ≡ Coordinate.listLength (Local.cells after)

    allLocalCNFsSatisfied :
      AllEncodedWindowCNFSatisfied
        codec rule
        (Whole.scanWindows machine before after)

open EncodedTransitionCNFCharacterization public

encodedTransitionCNFGivesLocality :
  ∀ {machine width rule before after}
    {codec : Weld.FixedWidthWindowCodec machine width} →
  EncodedTransitionCNFCharacterization
    codec rule before after →
  Locality.LocalityCharacterization
    machine rule before after
encodedTransitionCNFGivesLocality characterization =
  record
    { Locality.beforeInterior =
        beforeInterior characterization
    ; Locality.afterUnique =
        afterUnique characterization
    ; Locality.localityScan =
        record
          { Locality.ruleOccursInMachine =
              ruleOccursInMachine characterization
          ; Locality.sameRowLength =
              sameRowLength characterization
          ; Locality.everyWindowLegal =
              cnfAllWindowsToSemantic
                _
                (allLocalCNFsSatisfied characterization)
          }
    }

wholeRowCNFImpliesStep :
  ∀ {machine width rule before after}
    {codec : Weld.FixedWidthWindowCodec machine width} →
  EncodedTransitionCNFCharacterization
    codec rule before after →
  WF.WellFormedMachineStep machine before after
wholeRowCNFImpliesStep characterization =
  Locality.localityCharacterizationGivesWellFormedStep
    (encodedTransitionCNFGivesLocality characterization)

record ConcreteTapeWholeRowCNFWeldBoundary : Set where
  constructor concrete-tape-whole-row-cnf-weld-boundary
  field
    localCNFSemanticEquivalenceReused : Bool
    replicatedWindowCNFSemanticsPaid : Bool
    stepToWholeRowCNFPaid : Bool
    wholeRowCNFToStepPaid : Bool
    canonicalConcreteCodecSpecializationPaid : Bool
    placedGlobalAssignmentWeldPaid : Bool
    runToSATPaid : Bool
    satToRunPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeWholeRowCNFWeldBoundary :
  ConcreteTapeWholeRowCNFWeldBoundary
canonicalConcreteTapeWholeRowCNFWeldBoundary =
  concrete-tape-whole-row-cnf-weld-boundary
    true true true true false false false false false false
