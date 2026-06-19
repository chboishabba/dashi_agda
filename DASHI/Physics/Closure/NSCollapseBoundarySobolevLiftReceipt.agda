module DASHI.Physics.Closure.NSCollapseBoundarySobolevLiftReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

infixr 5 _∷_

------------------------------------------------------------------------
-- Self-contained receipt for the boundary Sobolev lift after finite Q(t).
--
-- The module records the boundary manifold ∂Ω_K, the finite-energy trace
-- control on smooth Navier-Stokes data, the finite L2 ratio control from
-- Q(t), the 2D boundary Sobolev embedding for s > 1, and the resulting
-- sup-bound on the boundary ratio.  The remaining blockers are kept open:
-- trace constants, boundary regularity, and H^s persistence.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

five : Nat
five =
  suc (suc (suc (suc (suc zero))))

------------------------------------------------------------------------
-- Stage data.

data SobolevLiftStage : Set where
  boundaryManifoldRecorded :
    SobolevLiftStage
  smoothFiniteEnergyHsTraceControlRecorded :
    SobolevLiftStage
  finiteQOfTFiniteL2RatioControlRecorded :
    SobolevLiftStage
  sobolevEmbeddingOnTwoDBoundaryRecorded :
    SobolevLiftStage
  resultingSupRatioBoundRecorded :
    SobolevLiftStage

sobolevLiftStageDescription :
  SobolevLiftStage → String
sobolevLiftStageDescription boundaryManifoldRecorded =
  "Record the boundary manifold ∂Ω_K."
sobolevLiftStageDescription
  smoothFiniteEnergyHsTraceControlRecorded =
  "Record smooth finite-energy NS data as supplying H^s trace control on ∂Ω_K."
sobolevLiftStageDescription
  finiteQOfTFiniteL2RatioControlRecorded =
  "Record finite Q(t) as giving L2 ratio control for <omega,e2>/g12 on ∂Ω_K."
sobolevLiftStageDescription
  sobolevEmbeddingOnTwoDBoundaryRecorded =
  "Use Sobolev embedding on the 2D boundary for s > 1."
sobolevLiftStageDescription
  resultingSupRatioBoundRecorded =
  "Conclude the resulting sup_x |<omega,e2>/g12| bound on ∂Ω_K."

record SobolevLiftStageRow : Set where
  field
    stage :
      SobolevLiftStage
    description :
      String
    descriptionIsCanonical :
      description ≡ sobolevLiftStageDescription stage

boundaryManifoldStageRow : SobolevLiftStageRow
boundaryManifoldStageRow =
  record
    { stage =
        boundaryManifoldRecorded
    ; description =
        sobolevLiftStageDescription boundaryManifoldRecorded
    ; descriptionIsCanonical =
        refl
    }

smoothFiniteEnergyHsTraceControlStageRow : SobolevLiftStageRow
smoothFiniteEnergyHsTraceControlStageRow =
  record
    { stage =
        smoothFiniteEnergyHsTraceControlRecorded
    ; description =
        sobolevLiftStageDescription
          smoothFiniteEnergyHsTraceControlRecorded
    ; descriptionIsCanonical =
        refl
    }

finiteQOfTFiniteL2RatioControlStageRow : SobolevLiftStageRow
finiteQOfTFiniteL2RatioControlStageRow =
  record
    { stage =
        finiteQOfTFiniteL2RatioControlRecorded
    ; description =
        sobolevLiftStageDescription
          finiteQOfTFiniteL2RatioControlRecorded
    ; descriptionIsCanonical =
        refl
    }

sobolevEmbeddingOnTwoDBoundaryStageRow : SobolevLiftStageRow
sobolevEmbeddingOnTwoDBoundaryStageRow =
  record
    { stage =
        sobolevEmbeddingOnTwoDBoundaryRecorded
    ; description =
        sobolevLiftStageDescription
          sobolevEmbeddingOnTwoDBoundaryRecorded
    ; descriptionIsCanonical =
        refl
    }

resultingSupRatioBoundStageRow : SobolevLiftStageRow
resultingSupRatioBoundStageRow =
  record
    { stage =
        resultingSupRatioBoundRecorded
    ; description =
        sobolevLiftStageDescription resultingSupRatioBoundRecorded
    ; descriptionIsCanonical =
        refl
    }

canonicalSobolevLiftStageRows : List SobolevLiftStageRow
canonicalSobolevLiftStageRows =
  boundaryManifoldStageRow
  ∷ smoothFiniteEnergyHsTraceControlStageRow
  ∷ finiteQOfTFiniteL2RatioControlStageRow
  ∷ sobolevEmbeddingOnTwoDBoundaryStageRow
  ∷ resultingSupRatioBoundStageRow
  ∷ []

sobolevLiftStageCount : Nat
sobolevLiftStageCount =
  listLength canonicalSobolevLiftStageRows

sobolevLiftStageCountIsFive :
  sobolevLiftStageCount ≡ five
sobolevLiftStageCountIsFive =
  refl

------------------------------------------------------------------------
-- Blockers.

data SobolevLiftBlocker : Set where
  traceConstantsOpen :
    SobolevLiftBlocker
  boundaryRegularityOpen :
    SobolevLiftBlocker
  hsPersistenceOpen :
    SobolevLiftBlocker

canonicalSobolevLiftBlockers : List SobolevLiftBlocker
canonicalSobolevLiftBlockers =
  traceConstantsOpen
  ∷ boundaryRegularityOpen
  ∷ hsPersistenceOpen
  ∷ []

sobolevLiftBlockerCount : Nat
sobolevLiftBlockerCount =
  listLength canonicalSobolevLiftBlockers

sobolevLiftBlockerCountIsThree :
  sobolevLiftBlockerCount ≡ suc (suc (suc zero))
sobolevLiftBlockerCountIsThree =
  refl

------------------------------------------------------------------------
-- Canonical statements and notes.

boundaryManifoldCanonicalName : String
boundaryManifoldCanonicalName =
  "∂Ω_K"

canonicalSobolevLiftReceiptStatement : String
canonicalSobolevLiftReceiptStatement =
  "Boundary Sobolev lift receipt: on ∂Ω_K, smooth finite-energy NS data provides H^s trace control, finite Q(t) provides L2 ratio control, 2D Sobolev embedding for s > 1 lifts this to a sup bound on <omega,e2>/g12, and the remaining blockers are trace constants, boundary regularity, and H^s persistence."

canonicalSobolevLiftBoundaryNotes : List String
canonicalSobolevLiftBoundaryNotes =
  "The receipt is about the boundary manifold ∂Ω_K, not the interior field."
  ∷ "The L2 ratio control is conditional on finite Q(t) at the relevant time."
  ∷ "The sup ratio bound uses 2D Sobolev embedding for s > 1 on the boundary."
  ∷ "Trace constants, boundary regularity, and H^s persistence remain open blockers."
  ∷ []

------------------------------------------------------------------------
-- Main receipt.

record NSCollapseBoundarySobolevLiftReceipt : Set where
  field
    boundaryManifold :
      String
    boundaryManifoldIsCanonical :
      boundaryManifold ≡ boundaryManifoldCanonicalName

    smoothFiniteEnergyHsTraceControl :
      Bool
    smoothFiniteEnergyHsTraceControlIsTrue :
      smoothFiniteEnergyHsTraceControl ≡ true

    finiteQOfTFiniteL2RatioControl :
      Bool
    finiteQOfTFiniteL2RatioControlIsTrue :
      finiteQOfTFiniteL2RatioControl ≡ true

    sobolevEmbeddingOnTwoDBoundaryForSgt1 :
      Bool
    sobolevEmbeddingOnTwoDBoundaryForSgt1IsTrue :
      sobolevEmbeddingOnTwoDBoundaryForSgt1 ≡ true

    resultingSupRatioBound :
      Bool
    resultingSupRatioBoundIsTrue :
      resultingSupRatioBound ≡ true

    traceConstantsResolved :
      Bool
    traceConstantsResolvedIsFalse :
      traceConstantsResolved ≡ false

    boundaryRegularityResolved :
      Bool
    boundaryRegularityResolvedIsFalse :
      boundaryRegularityResolved ≡ false

    hsPersistenceResolved :
      Bool
    hsPersistenceResolvedIsFalse :
      hsPersistenceResolved ≡ false

    stageRows :
      List SobolevLiftStageRow
    stageRowsAreCanonical :
      stageRows ≡ canonicalSobolevLiftStageRows

    stageRowCount :
      Nat
    stageRowCountIsFive :
      stageRowCount ≡ five

    blockers :
      List SobolevLiftBlocker
    blockersAreCanonical :
      blockers ≡ canonicalSobolevLiftBlockers

    collapseImpossible :
      Bool
    collapseImpossibleIsFalse :
      collapseImpossible ≡ false

    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

    receiptStatement :
      String
    receiptStatementIsCanonical :
      receiptStatement ≡ canonicalSobolevLiftReceiptStatement

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalSobolevLiftBoundaryNotes

open NSCollapseBoundarySobolevLiftReceipt public

canonicalNSCollapseBoundarySobolevLiftReceipt :
  NSCollapseBoundarySobolevLiftReceipt
canonicalNSCollapseBoundarySobolevLiftReceipt =
  record
    { boundaryManifold =
        boundaryManifoldCanonicalName
    ; boundaryManifoldIsCanonical =
        refl
    ; smoothFiniteEnergyHsTraceControl =
        true
    ; smoothFiniteEnergyHsTraceControlIsTrue =
        refl
    ; finiteQOfTFiniteL2RatioControl =
        true
    ; finiteQOfTFiniteL2RatioControlIsTrue =
        refl
    ; sobolevEmbeddingOnTwoDBoundaryForSgt1 =
        true
    ; sobolevEmbeddingOnTwoDBoundaryForSgt1IsTrue =
        refl
    ; resultingSupRatioBound =
        true
    ; resultingSupRatioBoundIsTrue =
        refl
    ; traceConstantsResolved =
        false
    ; traceConstantsResolvedIsFalse =
        refl
    ; boundaryRegularityResolved =
        false
    ; boundaryRegularityResolvedIsFalse =
        refl
    ; hsPersistenceResolved =
        false
    ; hsPersistenceResolvedIsFalse =
        refl
    ; stageRows =
        canonicalSobolevLiftStageRows
    ; stageRowsAreCanonical =
        refl
    ; stageRowCount =
        five
    ; stageRowCountIsFive =
        refl
    ; blockers =
        canonicalSobolevLiftBlockers
    ; blockersAreCanonical =
        refl
    ; collapseImpossible =
        false
    ; collapseImpossibleIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; receiptStatement =
        canonicalSobolevLiftReceiptStatement
    ; receiptStatementIsCanonical =
        refl
    ; receiptBoundary =
        canonicalSobolevLiftBoundaryNotes
    ; receiptBoundaryIsCanonical =
        refl
    }

------------------------------------------------------------------------
-- Projection lemmas.

boundaryManifoldProjection :
  boundaryManifold canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  boundaryManifoldCanonicalName
boundaryManifoldProjection =
  refl

smoothFiniteEnergyHsTraceControlProjection :
  smoothFiniteEnergyHsTraceControl
    canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  true
smoothFiniteEnergyHsTraceControlProjection =
  refl

finiteQOfTFiniteL2RatioControlProjection :
  finiteQOfTFiniteL2RatioControl
    canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  true
finiteQOfTFiniteL2RatioControlProjection =
  refl

sobolevEmbeddingOnTwoDBoundaryForSgt1Projection :
  sobolevEmbeddingOnTwoDBoundaryForSgt1
    canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  true
sobolevEmbeddingOnTwoDBoundaryForSgt1Projection =
  refl

resultingSupRatioBoundProjection :
  resultingSupRatioBound canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  true
resultingSupRatioBoundProjection =
  refl

traceConstantsResolvedProjection :
  traceConstantsResolved canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  false
traceConstantsResolvedProjection =
  refl

boundaryRegularityResolvedProjection :
  boundaryRegularityResolved canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  false
boundaryRegularityResolvedProjection =
  refl

hsPersistenceResolvedProjection :
  hsPersistenceResolved canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  false
hsPersistenceResolvedProjection =
  refl

collapseImpossibleProjection :
  collapseImpossible canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  false
collapseImpossibleProjection =
  refl

clayPromotionProjection :
  clayPromotion canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  false
clayPromotionProjection =
  refl

stageRowCountProjection :
  stageRowCount canonicalNSCollapseBoundarySobolevLiftReceipt
  ≡
  five
stageRowCountProjection =
  refl

