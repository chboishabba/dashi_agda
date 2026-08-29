module DASHI.Programmes.TestHarnessSelectedFamiliesExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Three literal dashitest experiment-family surfaces.
--
-- These families deliberately do not share one universal `accept` semantics.
------------------------------------------------------------------------

data SelectedTestFamily : Set where
  treeDiffusionBridge
  phase3QuotientLearning
  backendParity : SelectedTestFamily

record TreeDiffusionBridgeReceipt : Set₁ where
  constructor treeDiffusionBridgeReceipt
  field
    criterionDeclaredBeforeEvaluation : Set
    coarseToFineWithinDeclaredBaselineImprovement : Set
    fineToCoarseWithinDeclaredBaselineImprovement : Set
    asymmetryWithinDeclaredBudget : Set
    leakageCorrelationMeetsDeclaredCriterion : Set
    nonlocalLeakageWithinDeclaredBudget : Set

open TreeDiffusionBridgeReceipt public

record Phase3QuotientDiagnosticReceipt : Set₁ where
  constructor phase3QuotientDiagnosticReceipt
  field
    taskLossLogged : Set
    quotientLossLogged : Set
    mdlCostLogged : Set
    alphaScheduleLogged : Set
    planHitLogged : Set

open Phase3QuotientDiagnosticReceipt public

record BackendParityReceipt : Set₁ where
  constructor backendParityReceipt
  field
    criterionDeclaredBeforeEvaluation : Set
    declaredOutputRelationSatisfied : Set

open BackendParityReceipt public

record TestHarnessSelectedFamiliesBoundary : Set where
  constructor testHarnessSelectedFamiliesBoundary
  field
    phase3CompleteLogIsUniversalLearningTheorem : Bool
    phase3CompleteLogIsUniversalLearningTheoremIsFalse :
      phase3CompleteLogIsUniversalLearningTheorem ≡ false

    backendParityIsPerformanceEquivalence : Bool
    backendParityIsPerformanceEquivalenceIsFalse :
      backendParityIsPerformanceEquivalence ≡ false

    treeDiffusionFiniteAcceptanceIsUniversalTransportTheorem : Bool
    treeDiffusionFiniteAcceptanceIsUniversalTransportTheoremIsFalse :
      treeDiffusionFiniteAcceptanceIsUniversalTransportTheorem ≡ false

    familySpecificReceiptsMayEnterTypedEvidenceLayer : Bool
    familySpecificReceiptsMayEnterTypedEvidenceLayerIsTrue :
      familySpecificReceiptsMayEnterTypedEvidenceLayer ≡ true

canonicalTestHarnessSelectedFamiliesBoundary :
  TestHarnessSelectedFamiliesBoundary
canonicalTestHarnessSelectedFamiliesBoundary =
  testHarnessSelectedFamiliesBoundary
    false refl
    false refl
    false refl
    true refl
