module DASHI.Physics.Closure.NSClayPostCalc11HardWallStateAggregationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Post-Calc-11 hard-wall state aggregation receipt.
--
-- This module is self-contained and fail-closed.  It records the current
-- hard-wall dependency lattice as explicit rows and edges, keeps Clay=false,
-- and treats the closeable-package checkpoint as the canonical post-Calc-11
-- anchor.  No worker-authored modules are imported here.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- Canonical dependency rows.

data NSClayPostCalc11HardWallDependencyRow : Set where
  postCalc11BoundaryRow :
    NSClayPostCalc11HardWallDependencyRow
  closeablePackageCheckpointAt3ce9beb5Row :
    NSClayPostCalc11HardWallDependencyRow
  conditionalKornRow :
    NSClayPostCalc11HardWallDependencyRow
  hOmegaCtrlRow :
    NSClayPostCalc11HardWallDependencyRow
  qCommutatorRow :
    NSClayPostCalc11HardWallDependencyRow
  sobolevLiftRow :
    NSClayPostCalc11HardWallDependencyRow
  ratioAbsorptionRow :
    NSClayPostCalc11HardWallDependencyRow
  collapseImpossibleRow :
    NSClayPostCalc11HardWallDependencyRow
  gatewayFlagRow :
    NSClayPostCalc11HardWallDependencyRow
  submissionFlagRow :
    NSClayPostCalc11HardWallDependencyRow
  clayFalseRow :
    NSClayPostCalc11HardWallDependencyRow

canonicalNSClayPostCalc11HardWallDependencyRows :
  List NSClayPostCalc11HardWallDependencyRow
canonicalNSClayPostCalc11HardWallDependencyRows =
  postCalc11BoundaryRow
  ∷ closeablePackageCheckpointAt3ce9beb5Row
  ∷ conditionalKornRow
  ∷ hOmegaCtrlRow
  ∷ qCommutatorRow
  ∷ sobolevLiftRow
  ∷ ratioAbsorptionRow
  ∷ collapseImpossibleRow
  ∷ gatewayFlagRow
  ∷ submissionFlagRow
  ∷ clayFalseRow
  ∷ []

dependencyRowLabel :
  NSClayPostCalc11HardWallDependencyRow → String
dependencyRowLabel postCalc11BoundaryRow =
  "post-Calc-11 boundary recorded"
dependencyRowLabel closeablePackageCheckpointAt3ce9beb5Row =
  "closeable package checkpoint at 3ce9beb5"
dependencyRowLabel conditionalKornRow =
  "conditional Korn packet"
dependencyRowLabel hOmegaCtrlRow =
  "h_omega_ctrl from NS alone"
dependencyRowLabel qCommutatorRow =
  "Q commutator"
dependencyRowLabel sobolevLiftRow =
  "boundary Sobolev lift"
dependencyRowLabel ratioAbsorptionRow =
  "ratio absorption"
dependencyRowLabel collapseImpossibleRow =
  "collapseImpossible"
dependencyRowLabel gatewayFlagRow =
  "gateway flag"
dependencyRowLabel submissionFlagRow =
  "submission flag"
dependencyRowLabel clayFalseRow =
  "Clay=false"

canonicalNSClayPostCalc11HardWallDependencyRowLabels :
  List String
canonicalNSClayPostCalc11HardWallDependencyRowLabels =
  "post-Calc-11 boundary recorded"
  ∷ "closeable package checkpoint at 3ce9beb5"
  ∷ "conditional Korn packet"
  ∷ "h_omega_ctrl from NS alone"
  ∷ "Q commutator"
  ∷ "boundary Sobolev lift"
  ∷ "ratio absorption"
  ∷ "collapseImpossible"
  ∷ "gateway flag"
  ∷ "submission flag"
  ∷ "Clay=false"
  ∷ []

canonicalNSClayPostCalc11HardWallDependencyRowCount : Nat
canonicalNSClayPostCalc11HardWallDependencyRowCount =
  listLength canonicalNSClayPostCalc11HardWallDependencyRows

------------------------------------------------------------------------
-- Canonical dependency edges for the hard-wall lattice.

data NSClayPostCalc11HardWallDependencyEdge : Set where
  calc11ToCloseablePackageCheckpoint :
    NSClayPostCalc11HardWallDependencyEdge
  closeablePackageToConditionalKorn :
    NSClayPostCalc11HardWallDependencyEdge
  conditionalKornToHOmegaCtrl :
    NSClayPostCalc11HardWallDependencyEdge
  hOmegaCtrlToQCommutator :
    NSClayPostCalc11HardWallDependencyEdge
  qCommutatorToSobolevLift :
    NSClayPostCalc11HardWallDependencyEdge
  sobolevLiftToRatioAbsorption :
    NSClayPostCalc11HardWallDependencyEdge
  ratioAbsorptionToCollapseImpossible :
    NSClayPostCalc11HardWallDependencyEdge
  collapseImpossibleToGatewayFlag :
    NSClayPostCalc11HardWallDependencyEdge
  gatewayFlagToSubmissionFlag :
    NSClayPostCalc11HardWallDependencyEdge
  submissionFlagToClayFalse :
    NSClayPostCalc11HardWallDependencyEdge

canonicalNSClayPostCalc11HardWallDependencyEdges :
  List NSClayPostCalc11HardWallDependencyEdge
canonicalNSClayPostCalc11HardWallDependencyEdges =
  calc11ToCloseablePackageCheckpoint
  ∷ closeablePackageToConditionalKorn
  ∷ conditionalKornToHOmegaCtrl
  ∷ hOmegaCtrlToQCommutator
  ∷ qCommutatorToSobolevLift
  ∷ sobolevLiftToRatioAbsorption
  ∷ ratioAbsorptionToCollapseImpossible
  ∷ collapseImpossibleToGatewayFlag
  ∷ gatewayFlagToSubmissionFlag
  ∷ submissionFlagToClayFalse
  ∷ []

dependencyEdgeLabel :
  NSClayPostCalc11HardWallDependencyEdge → String
dependencyEdgeLabel calc11ToCloseablePackageCheckpoint =
  "post-Calc-11 boundary -> closeable package checkpoint at 3ce9beb5"
dependencyEdgeLabel closeablePackageToConditionalKorn =
  "closeable package checkpoint -> conditional Korn"
dependencyEdgeLabel conditionalKornToHOmegaCtrl =
  "conditional Korn -> h_omega_ctrl from NS alone"
dependencyEdgeLabel hOmegaCtrlToQCommutator =
  "h_omega_ctrl from NS alone -> Q commutator"
dependencyEdgeLabel qCommutatorToSobolevLift =
  "Q commutator -> boundary Sobolev lift"
dependencyEdgeLabel sobolevLiftToRatioAbsorption =
  "boundary Sobolev lift -> ratio absorption"
dependencyEdgeLabel ratioAbsorptionToCollapseImpossible =
  "ratio absorption -> collapseImpossible"
dependencyEdgeLabel collapseImpossibleToGatewayFlag =
  "collapseImpossible -> gateway flag"
dependencyEdgeLabel gatewayFlagToSubmissionFlag =
  "gateway flag -> submission flag"
dependencyEdgeLabel submissionFlagToClayFalse =
  "submission flag -> Clay=false"

canonicalNSClayPostCalc11HardWallDependencyEdgeLabels :
  List String
canonicalNSClayPostCalc11HardWallDependencyEdgeLabels =
  "post-Calc-11 boundary -> closeable package checkpoint at 3ce9beb5"
  ∷ "closeable package checkpoint -> conditional Korn"
  ∷ "conditional Korn -> h_omega_ctrl from NS alone"
  ∷ "h_omega_ctrl from NS alone -> Q commutator"
  ∷ "Q commutator -> boundary Sobolev lift"
  ∷ "boundary Sobolev lift -> ratio absorption"
  ∷ "ratio absorption -> collapseImpossible"
  ∷ "collapseImpossible -> gateway flag"
  ∷ "gateway flag -> submission flag"
  ∷ "submission flag -> Clay=false"
  ∷ []

canonicalNSClayPostCalc11HardWallDependencyEdgeCount : Nat
canonicalNSClayPostCalc11HardWallDependencyEdgeCount =
  listLength canonicalNSClayPostCalc11HardWallDependencyEdges

------------------------------------------------------------------------
-- Canonical state snapshot.

record NSClayPostCalc11HardWallState : Set where
  field
    postCalc11BoundaryRecorded :
      Bool
    postCalc11BoundaryRecordedIsTrue :
      postCalc11BoundaryRecorded ≡ true

    closeablePackageCheckpointAt3ce9beb5Recorded :
      Bool
    closeablePackageCheckpointAt3ce9beb5RecordedIsTrue :
      closeablePackageCheckpointAt3ce9beb5Recorded ≡ true

    conditionalKornRecorded :
      Bool
    conditionalKornRecordedIsFalse :
      conditionalKornRecorded ≡ false

    hOmegaCtrlRecorded :
      Bool
    hOmegaCtrlRecordedIsFalse :
      hOmegaCtrlRecorded ≡ false

    qCommutatorRecorded :
      Bool
    qCommutatorRecordedIsFalse :
      qCommutatorRecorded ≡ false

    sobolevLiftRecorded :
      Bool
    sobolevLiftRecordedIsFalse :
      sobolevLiftRecorded ≡ false

    ratioAbsorptionRecorded :
      Bool
    ratioAbsorptionRecordedIsFalse :
      ratioAbsorptionRecorded ≡ false

    collapseImpossibleRecorded :
      Bool
    collapseImpossibleRecordedIsFalse :
      collapseImpossibleRecorded ≡ false

    gatewayFlagRecorded :
      Bool
    gatewayFlagRecordedIsFalse :
      gatewayFlagRecorded ≡ false

    submissionFlagRecorded :
      Bool
    submissionFlagRecordedIsFalse :
      submissionFlagRecorded ≡ false

    clayFalseRecorded :
      Bool
    clayFalseRecordedIsFalse :
      clayFalseRecorded ≡ false

open NSClayPostCalc11HardWallState public

canonicalNSClayPostCalc11HardWallState :
  NSClayPostCalc11HardWallState
canonicalNSClayPostCalc11HardWallState =
  record
    { postCalc11BoundaryRecorded = true
    ; postCalc11BoundaryRecordedIsTrue = refl
    ; closeablePackageCheckpointAt3ce9beb5Recorded = true
    ; closeablePackageCheckpointAt3ce9beb5RecordedIsTrue = refl
    ; conditionalKornRecorded = false
    ; conditionalKornRecordedIsFalse = refl
    ; hOmegaCtrlRecorded = false
    ; hOmegaCtrlRecordedIsFalse = refl
    ; qCommutatorRecorded = false
    ; qCommutatorRecordedIsFalse = refl
    ; sobolevLiftRecorded = false
    ; sobolevLiftRecordedIsFalse = refl
    ; ratioAbsorptionRecorded = false
    ; ratioAbsorptionRecordedIsFalse = refl
    ; collapseImpossibleRecorded = false
    ; collapseImpossibleRecordedIsFalse = refl
    ; gatewayFlagRecorded = false
    ; gatewayFlagRecordedIsFalse = refl
    ; submissionFlagRecorded = false
    ; submissionFlagRecordedIsFalse = refl
    ; clayFalseRecorded = false
    ; clayFalseRecordedIsFalse = refl
    }

------------------------------------------------------------------------
-- Canonical ORCSLPGF summary.

record NSClayPostCalc11HardWallStateAggregationORCSLPGF : Set where
  constructor mkNSClayPostCalc11HardWallStateAggregationORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡
      "Worker 6 owns the post-Calc-11 hard-wall state aggregation receipt only."

    R :
      String
    RIsCanonical :
      R ≡
      "Aggregate the post-Calc-11 hard-wall state, keep the dependency lattice explicit, and keep Clay=false."

    C :
      String
    CIsCanonical :
      C ≡
      "NSClayPostCalc11HardWallStateAggregationReceipt.agda is a self-contained ledger surface over builtins only."

    S :
      String
    SIsCanonical :
      S ≡
      "Calc11 boundary recorded=true; closeable package checkpoint=true; conditional Korn, h_omega_ctrl, Q commutator, boundary Sobolev lift, ratio absorption, collapseImpossible, gateway, submission, and Clay=false are the current state rows."

    L :
      String
    LIsCanonical :
      L ≡
      "post-Calc-11 boundary -> closeable package checkpoint -> conditional Korn -> h_omega_ctrl -> Q commutator -> boundary Sobolev lift -> ratio absorption -> collapseImpossible -> gateway flag -> submission flag -> Clay=false"

    P :
      String
    PIsCanonical :
      P ≡
      "Use this as a fail-closed state aggregation only; no promotion is claimed."

    G :
      String
    GIsCanonical :
      G ≡
      "Gateway and submission remain false, and Clay remains false."

    F :
      String
    FIsCanonical :
      F ≡
      "The hard-wall chain stays explicit and unresolved after Calc 11."

open NSClayPostCalc11HardWallStateAggregationORCSLPGF public

canonicalNSClayPostCalc11HardWallStateAggregationORCSLPGF :
  NSClayPostCalc11HardWallStateAggregationORCSLPGF
canonicalNSClayPostCalc11HardWallStateAggregationORCSLPGF =
  mkNSClayPostCalc11HardWallStateAggregationORCSLPGF
    "Worker 6 owns the post-Calc-11 hard-wall state aggregation receipt only."
    refl
    "Aggregate the post-Calc-11 hard-wall state, keep the dependency lattice explicit, and keep Clay=false."
    refl
    "NSClayPostCalc11HardWallStateAggregationReceipt.agda is a self-contained ledger surface over builtins only."
    refl
    "Calc11 boundary recorded=true; closeable package checkpoint=true; conditional Korn, h_omega_ctrl, Q commutator, boundary Sobolev lift, ratio absorption, collapseImpossible, gateway, submission, and Clay=false are the current state rows."
    refl
    "post-Calc-11 boundary -> closeable package checkpoint -> conditional Korn -> h_omega_ctrl -> Q commutator -> boundary Sobolev lift -> ratio absorption -> collapseImpossible -> gateway flag -> submission flag -> Clay=false"
    refl
    "Use this as a fail-closed state aggregation only; no promotion is claimed."
    refl
    "Gateway and submission remain false, and Clay remains false."
    refl
    "The hard-wall chain stays explicit and unresolved after Calc 11."
    refl

------------------------------------------------------------------------
-- Receipt record.

record NSClayPostCalc11HardWallStateAggregationReceipt : Setω where
  field
    referenceCommit :
      String
    referenceCommitIsCanonical :
      referenceCommit ≡ "3ce9beb5"

    dependencyRows :
      List NSClayPostCalc11HardWallDependencyRow
    dependencyRowsAreCanonical :
      dependencyRows ≡ canonicalNSClayPostCalc11HardWallDependencyRows

    dependencyRowLabels :
      List String
    dependencyRowLabelsAreCanonical :
      dependencyRowLabels ≡ canonicalNSClayPostCalc11HardWallDependencyRowLabels

    dependencyRowCount :
      Nat
    dependencyRowCountIsCanonical :
      dependencyRowCount ≡ canonicalNSClayPostCalc11HardWallDependencyRowCount

    dependencyEdges :
      List NSClayPostCalc11HardWallDependencyEdge
    dependencyEdgesAreCanonical :
      dependencyEdges ≡ canonicalNSClayPostCalc11HardWallDependencyEdges

    dependencyEdgeLabels :
      List String
    dependencyEdgeLabelsAreCanonical :
      dependencyEdgeLabels ≡ canonicalNSClayPostCalc11HardWallDependencyEdgeLabels

    dependencyEdgeCount :
      Nat
    dependencyEdgeCountIsCanonical :
      dependencyEdgeCount ≡ canonicalNSClayPostCalc11HardWallDependencyEdgeCount

    state :
      NSClayPostCalc11HardWallState
    stateIsCanonical :
      state ≡ canonicalNSClayPostCalc11HardWallState

    orcslpgf :
      NSClayPostCalc11HardWallStateAggregationORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSClayPostCalc11HardWallStateAggregationORCSLPGF

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡
      ( "post-Calc-11 hard-wall state aggregation"
        ∷ "closeable package checkpoint at 3ce9beb5"
        ∷ "conditional Korn -> h_omega_ctrl -> Q commutator -> boundary Sobolev lift -> ratio absorption -> collapseImpossible"
        ∷ "gateway flag false"
        ∷ "submission flag false"
        ∷ "Clay=false"
        ∷ [] )

open NSClayPostCalc11HardWallStateAggregationReceipt public

canonicalNSClayPostCalc11HardWallStateAggregationReceipt :
  NSClayPostCalc11HardWallStateAggregationReceipt
canonicalNSClayPostCalc11HardWallStateAggregationReceipt =
  record
    { referenceCommit = "3ce9beb5"
    ; referenceCommitIsCanonical = refl
    ; dependencyRows = canonicalNSClayPostCalc11HardWallDependencyRows
    ; dependencyRowsAreCanonical = refl
    ; dependencyRowLabels = canonicalNSClayPostCalc11HardWallDependencyRowLabels
    ; dependencyRowLabelsAreCanonical = refl
    ; dependencyRowCount = canonicalNSClayPostCalc11HardWallDependencyRowCount
    ; dependencyRowCountIsCanonical = refl
    ; dependencyEdges = canonicalNSClayPostCalc11HardWallDependencyEdges
    ; dependencyEdgesAreCanonical = refl
    ; dependencyEdgeLabels = canonicalNSClayPostCalc11HardWallDependencyEdgeLabels
    ; dependencyEdgeLabelsAreCanonical = refl
    ; dependencyEdgeCount = canonicalNSClayPostCalc11HardWallDependencyEdgeCount
    ; dependencyEdgeCountIsCanonical = refl
    ; state = canonicalNSClayPostCalc11HardWallState
    ; stateIsCanonical = refl
    ; orcslpgf = canonicalNSClayPostCalc11HardWallStateAggregationORCSLPGF
    ; orcslpgfIsCanonical = refl
    ; receiptBoundary =
        "post-Calc-11 hard-wall state aggregation"
        ∷ "closeable package checkpoint at 3ce9beb5"
        ∷ "conditional Korn -> h_omega_ctrl -> Q commutator -> boundary Sobolev lift -> ratio absorption -> collapseImpossible"
        ∷ "gateway flag false"
        ∷ "submission flag false"
        ∷ "Clay=false"
        ∷ []
    ; receiptBoundaryIsCanonical = refl
    }

------------------------------------------------------------------------
-- Projection lemmas.

referenceCommitIs3ce9beb5 :
  referenceCommit canonicalNSClayPostCalc11HardWallStateAggregationReceipt
  ≡ "3ce9beb5"
referenceCommitIs3ce9beb5 = refl

projectDependencyRowsAreCanonical :
  dependencyRows canonicalNSClayPostCalc11HardWallStateAggregationReceipt
  ≡ canonicalNSClayPostCalc11HardWallDependencyRows
projectDependencyRowsAreCanonical = refl

projectDependencyRowLabelsAreCanonical :
  dependencyRowLabels canonicalNSClayPostCalc11HardWallStateAggregationReceipt
  ≡ canonicalNSClayPostCalc11HardWallDependencyRowLabels
projectDependencyRowLabelsAreCanonical = refl

dependencyRowCountIsEleven :
  dependencyRowCount canonicalNSClayPostCalc11HardWallStateAggregationReceipt
  ≡ 11
dependencyRowCountIsEleven = refl

projectDependencyEdgesAreCanonical :
  dependencyEdges canonicalNSClayPostCalc11HardWallStateAggregationReceipt
  ≡ canonicalNSClayPostCalc11HardWallDependencyEdges
projectDependencyEdgesAreCanonical = refl

projectDependencyEdgeLabelsAreCanonical :
  dependencyEdgeLabels canonicalNSClayPostCalc11HardWallStateAggregationReceipt
  ≡ canonicalNSClayPostCalc11HardWallDependencyEdgeLabels
projectDependencyEdgeLabelsAreCanonical = refl

dependencyEdgeCountIsTen :
  dependencyEdgeCount canonicalNSClayPostCalc11HardWallStateAggregationReceipt
  ≡ 10
dependencyEdgeCountIsTen = refl

projectPostCalc11BoundaryRecordedIsTrue :
  postCalc11BoundaryRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ true
projectPostCalc11BoundaryRecordedIsTrue = refl

projectCloseablePackageCheckpointAt3ce9beb5RecordedIsTrue :
  closeablePackageCheckpointAt3ce9beb5Recorded
    (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ true
projectCloseablePackageCheckpointAt3ce9beb5RecordedIsTrue = refl

projectConditionalKornRecordedIsFalse :
  conditionalKornRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectConditionalKornRecordedIsFalse = refl

projectHOmegaCtrlRecordedIsFalse :
  hOmegaCtrlRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectHOmegaCtrlRecordedIsFalse = refl

projectQCommutatorRecordedIsFalse :
  qCommutatorRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectQCommutatorRecordedIsFalse = refl

projectSobolevLiftRecordedIsFalse :
  sobolevLiftRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectSobolevLiftRecordedIsFalse = refl

projectRatioAbsorptionRecordedIsFalse :
  ratioAbsorptionRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectRatioAbsorptionRecordedIsFalse = refl

projectCollapseImpossibleRecordedIsFalse :
  collapseImpossibleRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectCollapseImpossibleRecordedIsFalse = refl

projectGatewayFlagRecordedIsFalse :
  gatewayFlagRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectGatewayFlagRecordedIsFalse = refl

projectSubmissionFlagRecordedIsFalse :
  submissionFlagRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectSubmissionFlagRecordedIsFalse = refl

projectClayFalseRecordedIsFalse :
  clayFalseRecorded (state canonicalNSClayPostCalc11HardWallStateAggregationReceipt)
  ≡ false
projectClayFalseRecordedIsFalse = refl

projectReceiptBoundaryIsCanonical :
  receiptBoundary canonicalNSClayPostCalc11HardWallStateAggregationReceipt
  ≡ ( "post-Calc-11 hard-wall state aggregation"
      ∷ "closeable package checkpoint at 3ce9beb5"
      ∷ "conditional Korn -> h_omega_ctrl -> Q commutator -> boundary Sobolev lift -> ratio absorption -> collapseImpossible"
      ∷ "gateway flag false"
      ∷ "submission flag false"
      ∷ "Clay=false"
      ∷ [] )
projectReceiptBoundaryIsCanonical = refl
