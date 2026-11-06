module DASHI.Mathematics.Complexity.ConcreteTapeGuardedDecodedTransitionExact where

------------------------------------------------------------------------
-- SINGLE GUARDED GLOBAL SAT MODEL -> GENUINE DECODED MACHINE STEP.
--
-- The premise is the ACTUAL guardedGlobalCookLevinCNF on the one
-- extended assignment. The only independent hypotheses are the
-- established original interior-head and semantic-window proofs.
-- No independent NoGhost witness is supplied: it is constructed
-- using the original row endpoints and same-object Fin decode.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem
import DASHI.Mathematics.Complexity.ConcreteTapeGuardedGlobalCookLevinCNFExact as Guarded
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedEndcapSameObjectExact as Same
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedTransitionStepExact as Step
import DASHI.Mathematics.Complexity.ConcreteTapeAfterUniqueFromLocalityExact as AfterUnique
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

guardedSATNoGhostAtTime :
  ∀ {machine steps timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (colsMinusOne : Nat)
    (timeSlot : Global.Slot timeIndex steps)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne)))
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne)))
    (semantics :
      Scan.AllRawWindowsSemantic stateCoverage symbolCoverage nonempty
        timeSlot (FormulaSem.baseTraceBits assignment)
        (Transition.allWindowStarts (suc colsMinusOne)))
    (interior :
      Character.InteriorHeadConfiguration machine
        (Step.decodedBeforeRow stateCoverage symbolCoverage
          timeSlot (FormulaSem.baseTraceBits assignment))) →
  CNF.evaluateCNF
    (Guarded.guardedGlobalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps colsMinusOne initialTarget)
    assignment ≡ true →
  AfterUnique.NoGhostContextBoundaries
    (Step.decodedTimeLocalityScan stateCoverage symbolCoverage nonempty
      timeSlot (FormulaSem.baseTraceBits assignment) semantics)
    interior
guardedSATNoGhostAtTime
    stateCoverage symbolCoverage nonempty colsMinusOne
    timeSlot initialTarget assignment semantics interior accepted =
  AfterUnique.noGhostFromAfterRowEndcaps
    (Step.decodedTimeLocalityScan stateCoverage symbolCoverage nonempty
      timeSlot (FormulaSem.baseTraceBits assignment) semantics)
    interior
    (Same.front endcaps)
    (Same.back endcaps)
  where
    parts = Guarded.guardedGlobalCookLevinCNFSound
      stateCoverage symbolCoverage nonempty
      _ colsMinusOne initialTarget assignment accepted

    endcaps = Same.globalCNFToDecodedRowEndcaps
      stateCoverage symbolCoverage colsMinusOne
      (Global.nextSlotInSucc timeSlot) assignment
      (Guarded.globalEndcapCNFTrue parts)

guardedSATDecodedMachineStep :
  ∀ {machine steps timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (colsMinusOne : Nat)
    (timeSlot : Global.Slot timeIndex steps)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne)))
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne)))
    (semantics :
      Scan.AllRawWindowsSemantic stateCoverage symbolCoverage nonempty
        timeSlot (FormulaSem.baseTraceBits assignment)
        (Transition.allWindowStarts (suc colsMinusOne)))
    (interior :
      Character.InteriorHeadConfiguration machine
        (Step.decodedBeforeRow stateCoverage symbolCoverage
          timeSlot (FormulaSem.baseTraceBits assignment))) →
  CNF.evaluateCNF
    (Guarded.guardedGlobalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps colsMinusOne initialTarget)
    assignment ≡ true →
  WF.WellFormedMachineStep machine
    (Step.decodedBeforeRow stateCoverage symbolCoverage
      timeSlot (FormulaSem.baseTraceBits assignment))
    (Step.decodedAfterRow stateCoverage symbolCoverage
      timeSlot (FormulaSem.baseTraceBits assignment))
guardedSATDecodedMachineStep stateCoverage symbolCoverage nonempty
    colsMinusOne timeSlot initialTarget assignment semantics interior
    accepted =
  Step.decodedAdjacentRowsFormMachineStep
    stateCoverage symbolCoverage nonempty
    timeSlot (FormulaSem.baseTraceBits assignment)
    interior semantics
    (guardedSATNoGhostAtTime
      stateCoverage symbolCoverage nonempty colsMinusOne
      timeSlot initialTarget assignment semantics interior accepted)
