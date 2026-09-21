module DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact where

------------------------------------------------------------------------
-- P7: ONE SATISFYING COOK--LEVIN FORMULA -> ACTUAL ACCEPTING RUN
--
-- Prize-facing capstone for the soundness direction only:
--
--   satisfying global SAT assignment
--      -> exact guarded literal row 0
--      -> semantic transition scan
--      -> P4 WellFormedTapeRun
--      -> acceptance witness occurs in the very same final decoded row
--      -> uniqueness of the final head identifies its state as accepting
--      -> existing AcceptingWellFormedRun
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedRunInductionExact as RunInduction
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceDecodedFinalRowExact as AcceptFinal
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceEndpointSoundExact as AcceptSound
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeInitialDecodeSameObjectExact as Initial
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedWindowSameObjectExact as Same
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Exact guarded input target bits
------------------------------------------------------------------------

guardedInitialBits :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (steps : Nat) →
  CNF.Bits
    (Decode.RowBitsWidth machine
      (Guard.guardedInitialCols input steps))
guardedInitialBits {machine}
    stateCoverage symbolCoverage input steps
    rewrite sym (Guard.guardedInitialCellCount input steps) =
  Flat.encodeRow stateCoverage symbolCoverage
    (Guard.guardedInitialRow input steps)

guardedInitialBitsDecode :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (steps : Nat) →
  Decode.decodeRow stateCoverage symbolCoverage
    (Guard.guardedInitialCols input steps)
    (guardedInitialBits
      stateCoverage symbolCoverage input steps)
  ≡
  Guard.guardedInitialRow input steps
guardedInitialBitsDecode
    stateCoverage symbolCoverage input steps
    rewrite sym (Guard.guardedInitialCellCount input steps) =
  Initial.decodeRow_encodeRow stateCoverage symbolCoverage
    (Guard.guardedInitialRow input steps)

------------------------------------------------------------------------
-- Row 0 in the base trace is the exact endpoint pullback.
------------------------------------------------------------------------

baseRowZeroBits_eq_endpointInitialBits :
  ∀ {machine}
    (steps cols : Nat)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  Global.rowSliceBits
    (Global.here {remaining = steps})
    (FormulaSem.baseTraceBits assignment)
  ≡
  Rename.pullbackBits
    Endpoint.initialRowExtendedRename
    assignment
baseRowZeroBits_eq_endpointInitialBits
    {machine} steps cols assignment =
  Same.pullbackCompose
    (Global.globalRowRename
      (Global.here {remaining = steps}))
    Endpoint.liftBaseIndex
    assignment

decodedStart_eq_guardedInitial :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (steps : Nat)
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps
          (Guard.guardedInitialCols input steps)))
    (semantics :
      FormulaSem.SatisfyingGlobalFormulaSemantics
        stateCoverage symbolCoverage
        _
        steps (Guard.guardedInitialCols input steps)
        (guardedInitialBits
          stateCoverage symbolCoverage input steps)
        assignment) →
  Decode.decodeRow stateCoverage symbolCoverage
    (Guard.guardedInitialCols input steps)
    (Global.rowSliceBits
      (Global.here {remaining = steps})
      (FormulaSem.baseTraceBits assignment))
  ≡
  Guard.guardedInitialRow input steps
decodedStart_eq_guardedInitial
    stateCoverage symbolCoverage input steps assignment semantics =
  trans
    (cong
      (Decode.decodeRow stateCoverage symbolCoverage _)
      (trans
        (baseRowZeroBits_eq_endpointInitialBits
          steps _ assignment)
        (FormulaSem.initialRowBitsExact semantics)))
    (guardedInitialBitsDecode
      stateCoverage symbolCoverage input steps)

------------------------------------------------------------------------
-- Unique-headedness identifies any headed occurrence's state.
------------------------------------------------------------------------

plainCellsNoHeaded :
  ∀ {State Symbol : Set}
    {cells : List (Local.TapeCell State Symbol)}
    {n : Nat} {q : State} {a : Symbol} →
  WF.PlainCells cells →
  Indexed.At n (Local.headed q a) cells →
  ⊥
plainCellsNoHeaded WF.plainNil ()
plainCellsNoHeaded (WF.plainCons plain) (Indexed.there occurs) =
  plainCellsNoHeaded plain occurs

uniqueHeadedStates :
  ∀ {State Symbol : Set}
    {cells : List (Local.TapeCell State Symbol)}
    {i j : Nat}
    {q r : State}
    {a b : Symbol} →
  WF.ExactlyOneHead cells →
  Indexed.At i (Local.headed q a) cells →
  Indexed.At j (Local.headed r b) cells →
  q ≡ r
uniqueHeadedStates
    (WF.headHere restPlain)
    Indexed.here Indexed.here =
  refl
uniqueHeadedStates
    (WF.headHere restPlain)
    Indexed.here (Indexed.there right) =
  ⊥-elim (plainCellsNoHeaded restPlain right)
uniqueHeadedStates
    (WF.headHere restPlain)
    (Indexed.there left) Indexed.here =
  ⊥-elim (plainCellsNoHeaded restPlain left)
uniqueHeadedStates
    (WF.headHere restPlain)
    (Indexed.there left) (Indexed.there right) =
  ⊥-elim (plainCellsNoHeaded restPlain left)
uniqueHeadedStates
    (WF.plainBefore unique)
    (Indexed.there left) (Indexed.there right) =
  uniqueHeadedStates unique left right

------------------------------------------------------------------------
-- The head exhibited by an InteriorHeadConfiguration really occurs.
------------------------------------------------------------------------

headAtAfterPlainPrefix :
  ∀ {State Symbol : Set}
    {prefix suffix : List (Local.TapeCell State Symbol)}
    {left read right : Symbol}
    {q : State} →
  WF.PlainCells prefix →
  Σ Nat (λ n →
    Indexed.At n
      (Local.headed q read)
      (Local.append prefix
        (Local.plain left
          ∷ Local.headed q read
          ∷ Local.plain right
          ∷ suffix)))
headAtAfterPlainPrefix WF.plainNil =
  suc zero , Indexed.there Indexed.here
headAtAfterPlainPrefix (WF.plainCons prefixPlain)
    with headAtAfterPlainPrefix prefixPlain
... | n , occurrence =
  suc n , Indexed.there occurrence

transportAtList :
  ∀ {A : Set} {n : Nat} {x : A}
    {left right : List A} →
  left ≡ right →
  Indexed.At n x left →
  Indexed.At n x right
transportAtList refl occurrence = occurrence

interiorHeadOccurrence :
  ∀ {machine row}
    (interior :
      Character.InteriorHeadConfiguration machine row) →
  Σ Nat (λ n →
    Indexed.At n
      (Local.headed
        (Character.headState interior)
        (Character.readSymbol interior))
      (Local.cells row))
interiorHeadOccurrence interior
    with headAtAfterPlainPrefix
      (Character.prefixPlain interior)
... | n , occurrence =
  n ,
  transportAtList
    (sym (Character.rowShape interior))
    occurrence

------------------------------------------------------------------------
-- Transport endpoint acceptance into the P4 finish row.
------------------------------------------------------------------------

transportAcceptanceOccurrenceToFinish :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols))
    (finish : Local.TapeRow machine) →
  finish ≡
    Decode.decodeRow stateCoverage symbolCoverage cols
      (Global.rowSliceBits
        (Endpoint.finalRowSlot steps)
        (FormulaSem.baseTraceBits assignment)) →
  AcceptFinal.AcceptingCellInDecodedFinalRow
    stateCoverage symbolCoverage assignment →
  Σ Nat (λ n →
    Σ (Local.Symbol machine) (λ symbol →
      Indexed.At n
        (Local.headed (Local.acceptingState machine) symbol)
        (Local.cells finish)))
transportAcceptanceOccurrenceToFinish
    stateCoverage symbolCoverage assignment
    finish finishEq witness =
  Fin.toℕ (AcceptFinal.index witness) ,
  AcceptFinal.symbol witness ,
  transportAtList
    (cong Local.cells (sym finishEq))
    (AcceptFinal.occurs witness)
  where
    open import Data.Fin.Base as Fin

------------------------------------------------------------------------
-- P7 capstone
------------------------------------------------------------------------

record SatisfyingAssignmentAcceptingRun
    {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) : Set₁ where
  field
    rows : List (Local.TapeRow machine)
    finish : Local.TapeRow machine
    certificate :
      Accepting.AcceptingWellFormedRun
        machine
        (Guard.guardedInitialRow input steps)
        rows
        finish

open SatisfyingAssignmentAcceptingRun public

satisfyingCookLevinAssignmentToAcceptingRun :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat)
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps
          (Guard.guardedInitialCols input steps))) →
  CNF.evaluateCNF
    (GlobalCNF.globalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps (Guard.guardedInitialCols input steps)
      (guardedInitialBits
        stateCoverage symbolCoverage input steps))
    assignment
  ≡ true →
  SatisfyingAssignmentAcceptingRun input steps
satisfyingCookLevinAssignmentToAcceptingRun
    {machine} stateCoverage symbolCoverage nonempty
    input steps assignment accepted =
  record
    { rows = RunInduction.rows runResult
    ; finish = RunInduction.finish runResult
    ; certificate = record
        { Accepting.initial = guardedInitialIsInitial
        ; Accepting.run =
            RunInduction.transportRunStart
              (sym startEq)
              (RunInduction.run runResult)
        ; Accepting.accepting = acceptingFinish
        }
    }
  where
    cols = Guard.guardedInitialCols input steps

    semantics =
      FormulaSem.satisfyingGlobalFormulaSemantics
        stateCoverage symbolCoverage nonempty
        steps cols
        (guardedInitialBits
          stateCoverage symbolCoverage input steps)
        assignment accepted

    baseBits =
      FormulaSem.baseTraceBits assignment

    semanticScan =
      Scan.globalTransitionCNF_to_semanticScan
        stateCoverage symbolCoverage nonempty
        steps cols baseBits
        (FormulaSem.transitionCNFTrue semantics)

    allSemantic =
      Scan.everyTimeEveryWindowSemantic semanticScan

    start =
      Decode.decodeRow stateCoverage symbolCoverage cols
        (Global.rowSliceBits
          (Global.here {remaining = steps}) baseBits)

    startEq :
      start ≡ Guard.guardedInitialRow input steps
    startEq =
      decodedStart_eq_guardedInitial
        stateCoverage symbolCoverage input steps
        assignment semantics

    literalUnique :
      WF.ExactlyOneHead
        (Local.cells (Guard.guardedInitialRow input steps))
    literalUnique =
      Margin.interiorExactlyOneHead
        (Guard.guardedInitialInterior input steps)
      where
        import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin

    startUnique :
      WF.ExactlyOneHead (Local.cells start)
    startUnique =
      WF.transportExactlyOneHead
        (cong Local.cells (sym startEq))
        literalUnique

    startMargin :
      DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact.HeadMargin
        (suc steps) (Local.cells start)
    startMargin =
      RunInduction.transportMarginRow
        (sym startEq)
        (Guard.guardedInitialMargin input steps)

    runResult =
      RunInduction.decodedAllSlotsRun
        stateCoverage symbolCoverage nonempty
        steps baseBits allSemantic
        startUnique startMargin

    finishEq =
      RunInduction.decodedAllSlotsRun_finish_eq_finalGlobalRow
        stateCoverage symbolCoverage nonempty
        steps baseBits allSemantic
        startUnique startMargin

    endpointCell =
      AcceptFinal.acceptanceWitnessCellIsDecodedFinalCell
        stateCoverage symbolCoverage assignment
        (FormulaSem.acceptingFinalCell semantics)

    acceptingInFinish =
      transportAcceptanceOccurrenceToFinish
        stateCoverage symbolCoverage assignment
        (RunInduction.finish runResult)
        finishEq endpointCell

    finalInterior =
      RunInduction.finalInterior runResult

    interiorOccurrence =
      interiorHeadOccurrence finalInterior

    acceptingStateEq :
      Character.headState finalInterior
      ≡ Local.acceptingState machine
    acceptingStateEq
      with interiorOccurrence | acceptingInFinish
    ... | i , headOccurs | j , symbol , acceptingOccurs =
      uniqueHeadedStates
        (RunInduction.finalUnique runResult)
        headOccurs acceptingOccurs

    acceptingFinish :
      Accepting.AcceptingInteriorRow
        machine (RunInduction.finish runResult)
    acceptingFinish = record
      { Accepting.interior = finalInterior
      ; Accepting.headIsAccepting = acceptingStateEq
      }

    guardedInitialIsInitial :
      Accepting.InitialInteriorRow
        machine (Guard.guardedInitialRow input steps)
    guardedInitialIsInitial = record
      { Accepting.interior =
          Guard.guardedInitialInterior input steps
      ; Accepting.headIsInitial =
          Guard.guardedInitialState input steps
      }

record SATToAcceptingRunReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    guardedInitialBitsPaid : Bool
    rowZeroSameObjectPaid : Bool
    transitionScanPaid : Bool
    tStepRunInductionPaid : Bool
    runFinishSameFinalRowPaid : Bool
    acceptanceWitnessUniquenessPaid : Bool
    satToAcceptingRunPaid : Bool

satToAcceptingRunReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  SATToAcceptingRunReceipt machine
satToAcceptingRunReceipt machine = record
  { guardedInitialBitsPaid = true
  ; rowZeroSameObjectPaid = true
  ; transitionScanPaid = true
  ; tStepRunInductionPaid = true
  ; runFinishSameFinalRowPaid = true
  ; acceptanceWitnessUniquenessPaid = true
  ; satToAcceptingRunPaid = true
  }
