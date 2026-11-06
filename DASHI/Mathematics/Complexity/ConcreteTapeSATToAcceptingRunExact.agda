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
open import Data.Product using (Σ; _,_; proj₁; proj₂)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedRunInductionExact as RunInduction
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedRunLengthExact as RunLength
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceDecodedFinalRowExact as AcceptFinal
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptanceEndpointSoundExact as AcceptSound
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeInitialDecodeSameObjectExact as Initial
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedWindowSameObjectExact as Same
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedTransitionStepExact as Step
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Exact guarded input target bits
------------------------------------------------------------------------

canonicalGuardedInitialCellCount :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Canonical.listLength
    (Local.cells {machine} (Guard.guardedInitialRow input steps))
  ≡ Guard.guardedInitialCols input steps
canonicalGuardedInitialCellCount {machine} input steps =
  trans
    (sym (Guard.canonical_eq_coordinate
      (Guard.guardedInitialCells {machine} input steps)))
    (Guard.guardedInitialCellCount input steps)

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
    stateCoverage symbolCoverage input steps =
  subst CNF.Bits
    (cong (Decode.RowBitsWidth machine)
      (canonicalGuardedInitialCellCount input steps))
    (Flat.encodeRow {machine} stateCoverage symbolCoverage
      (Guard.guardedInitialRow input steps))

guardedInitialBitsDecode_helper :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (row : Local.TapeRow machine)
    (cols : Nat)
    (e : Canonical.listLength (Local.cells {machine} row) ≡ cols) →
  Decode.decodeRow {machine} stateCoverage symbolCoverage cols
    (subst CNF.Bits (cong (Decode.RowBitsWidth machine) e)
      (Flat.encodeRow {machine} stateCoverage symbolCoverage row))
  ≡ row
guardedInitialBitsDecode_helper {machine} stateCoverage symbolCoverage row ._ refl =
  Initial.decodeRow_encodeRow {machine} stateCoverage symbolCoverage row

guardedInitialBitsDecode :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (steps : Nat) →
  Decode.decodeRow {machine} stateCoverage symbolCoverage
    (Guard.guardedInitialCols input steps)
    (guardedInitialBits
      stateCoverage symbolCoverage input steps)
  ≡
  Guard.guardedInitialRow input steps
guardedInitialBitsDecode {machine}
    stateCoverage symbolCoverage input steps =
  guardedInitialBitsDecode_helper {machine}
    stateCoverage symbolCoverage
    (Guard.guardedInitialRow input steps)
    (Guard.guardedInitialCols input steps)
    (canonicalGuardedInitialCellCount input steps)

------------------------------------------------------------------------
-- Row 0 in the base trace is the exact endpoint pullback.
------------------------------------------------------------------------

baseRowZeroBits_eq_endpointInitialBits :
  ∀ {machine}
    (steps cols : Nat)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  Global.rowSliceBits {machine} {steps} {cols}
    (Global.here {remaining = steps})
    (FormulaSem.baseTraceBits {machine} {steps} {cols} assignment)
  ≡
  Rename.pullbackBits
    (Endpoint.initialRowExtendedRename {machine} {steps} {cols})
    assignment
baseRowZeroBits_eq_endpointInitialBits
    {machine} steps cols assignment =
  sym
    (Same.pullbackCompose
      (Global.globalRowRename {machine} {steps} {cols}
        (Global.here {remaining = steps}))
      (Endpoint.liftBaseIndex {machine} {steps} {cols})
      assignment)

decodedStart_eq_guardedInitial :
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
          (Guard.guardedInitialCols input steps)))
    (semantics :
      FormulaSem.SatisfyingGlobalFormulaSemantics {machine}
        stateCoverage symbolCoverage
        nonempty
        steps (Guard.guardedInitialCols input steps)
        (guardedInitialBits
          stateCoverage symbolCoverage input steps)
        assignment) →
  Decode.decodeRow {machine} stateCoverage symbolCoverage
    (Guard.guardedInitialCols input steps)
    (Global.rowSliceBits {machine} {steps} {Guard.guardedInitialCols input steps}
      (Global.here {remaining = steps})
      (FormulaSem.baseTraceBits {machine} {steps} {Guard.guardedInitialCols input steps} assignment))
  ≡
  Guard.guardedInitialRow input steps
decodedStart_eq_guardedInitial {machine}
    stateCoverage symbolCoverage nonempty input steps assignment semantics =
  trans
    (cong
      (Decode.decodeRow {machine} stateCoverage symbolCoverage
        (Guard.guardedInitialCols input steps))
      (trans
        (baseRowZeroBits_eq_endpointInitialBits {machine}
          steps (Guard.guardedInitialCols input steps) assignment)
        (FormulaSem.initialRowBitsExact semantics)))
    (guardedInitialBitsDecode {machine}
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
    Decode.decodeRow {machine} stateCoverage symbolCoverage cols
      (Global.rowSliceBits {machine} {steps} {cols}
        (Endpoint.finalRowSlot steps)
        (FormulaSem.baseTraceBits {machine} {steps} {cols} assignment)) →
  AcceptFinal.AcceptingCellInDecodedFinalRow {machine} {steps} {cols}
    stateCoverage symbolCoverage assignment →
  Σ Nat (λ n →
    Σ (Local.Symbol machine) (λ symbol →
      Indexed.At n
        (Local.headed (Local.acceptingState machine) symbol)
        (Local.cells {machine} finish)))
transportAcceptanceOccurrenceToFinish
    {machine = machine} {steps = steps} {cols = cols}
    stateCoverage symbolCoverage assignment
    finish finishEq witness =
  Fin.toℕ (AcceptFinal.index witness) ,
  AcceptFinal.symbol witness ,
  transportAtList
    (cong (Local.cells {machine}) (sym finishEq))
    (AcceptFinal.occurs witness)
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

    exactLength :
      Accepting.acceptingRunLength certificate ≡ steps

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
  Step.AllTimeStepsBoundaryGuards {machine} {steps} {Guard.guardedInitialCols input steps}
    stateCoverage symbolCoverage nonempty
    (FormulaSem.baseTraceBits {machine} {steps} {Guard.guardedInitialCols input steps} assignment) →
  SatisfyingAssignmentAcceptingRun input steps
satisfyingCookLevinAssignmentToAcceptingRun
    {machine} stateCoverage symbolCoverage nonempty
    input steps assignment accepted guards =
  record
    { rows = RunInduction.rows runResult
    ; finish = RunInduction.finish runResult
    ; certificate = certificateExact
    ; exactLength = certificateExactLength
    }
  where
    cols = Guard.guardedInitialCols input steps

    semantics =
      FormulaSem.satisfyingGlobalFormulaSemantics {machine}
        stateCoverage symbolCoverage nonempty
        steps cols
        (guardedInitialBits
          stateCoverage symbolCoverage input steps)
        assignment accepted

    baseBits =
      FormulaSem.baseTraceBits {machine} {steps} {cols} assignment

    semanticScan =
      Scan.globalTransitionCNF_to_semanticScan
        stateCoverage symbolCoverage nonempty
        steps cols baseBits
        (FormulaSem.transitionCNFTrue semantics)

    allSemantic =
      Scan.everyTimeEveryWindowSemantic semanticScan

    start =
      Decode.decodeRow {machine} stateCoverage symbolCoverage cols
        (Global.rowSliceBits {machine} {steps} {cols}
          (Global.here {remaining = steps}) baseBits)

    startEq :
      start ≡ Guard.guardedInitialRow input steps
    startEq =
      decodedStart_eq_guardedInitial {machine}
        stateCoverage symbolCoverage nonempty input steps
        assignment semantics

    literalUnique :
      WF.ExactlyOneHead
        (Local.cells {machine} (Guard.guardedInitialRow input steps))
    literalUnique =
      Margin.interiorExactlyOneHead
        (Guard.guardedInitialInterior input steps)

    startUnique :
      WF.ExactlyOneHead (Local.cells {machine} start)
    startUnique =
      WF.transportExactlyOneHead
        (cong (Local.cells {machine}) (sym startEq))
        literalUnique

    startMargin :
      Margin.HeadMargin
        (suc steps) (Local.cells {machine} start)
    startMargin =
      RunInduction.transportMarginRow {machine}
        (sym startEq)
        (Guard.guardedInitialMargin input steps)

    runResult =
      RunInduction.decodedAllSlotsRun {machine} {cols}
        stateCoverage symbolCoverage nonempty
        steps baseBits allSemantic
        startUnique startMargin guards

    finishEq =
      RunInduction.decodedAllSlotsRun_finish_eq_finalGlobalRow {machine} {cols}
        stateCoverage symbolCoverage nonempty
        steps baseBits allSemantic
        startUnique startMargin guards

    endpointCell =
      AcceptFinal.acceptanceWitnessCellIsDecodedFinalCell
        {machine} {steps} {cols}
        stateCoverage symbolCoverage assignment
        (FormulaSem.acceptingFinalCell semantics)

    acceptingInFinish =
      transportAcceptanceOccurrenceToFinish
        {machine} {steps} {cols}
        stateCoverage symbolCoverage assignment
        (RunInduction.finish runResult)
        finishEq endpointCell

    finalInterior =
      RunInduction.finalInterior runResult

    interiorOccurrence =
      interiorHeadOccurrence {machine} finalInterior

    acceptingStateEq :
      Character.headState finalInterior
      ≡ Local.acceptingState machine
    acceptingStateEq =
      uniqueHeadedStates
        (RunInduction.finalUnique runResult)
        (proj₂ interiorOccurrence)
        (proj₂ (proj₂ acceptingInFinish))

    acceptingFinish :
      Accepting.AcceptingInteriorRow
        machine (RunInduction.finish runResult)
    acceptingFinish = record
      { interior = finalInterior
      ; headIsAccepting = acceptingStateEq
      }

    guardedInitialIsInitial :
      Accepting.InitialInteriorRow
        machine (Guard.guardedInitialRow input steps)
    guardedInitialIsInitial = record
      { interior =
          Guard.guardedInitialInterior input steps
      ; headIsInitial =
          Guard.guardedInitialState input steps
      }

    certificateExact :
      Accepting.AcceptingWellFormedRun
        machine
        (Guard.guardedInitialRow input steps)
        (RunInduction.rows runResult)
        (RunInduction.finish runResult)
    certificateExact = record
      { initial = guardedInitialIsInitial
      ; run =
          RunInduction.transportRunStart
            (sym startEq)
            (RunInduction.run runResult)
      ; accepting = acceptingFinish
      }

    certificateExactLength :
      Accepting.acceptingRunLength certificateExact ≡ steps
    certificateExactLength =
      trans
        (RunLength.transportRunStart_length
          (sym startEq)
          (RunInduction.run runResult))
        (RunLength.decodedAllSlotsRun_length
          stateCoverage symbolCoverage nonempty
          steps baseBits allSemantic
          startUnique startMargin guards)

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
