module DASHI.Core.ResidualObligationPropagationExact where

------------------------------------------------------------------------
-- RESIDUAL OBLIGATION PROPAGATION
--
-- Generic fail-closed theorem pattern: unresolved obligations survive promotion
-- until an explicit discharge witness is supplied.  Inspired by the explicit
-- remainder ledgers in Wette recovery (#615), TSFV realization (#621), NS
-- antisymmetry-defect accounting (#623), RH nuisance/error ledgers (#604/#622),
-- and existing DASHI justice/history residuals.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record ResidualFlow : Set₁ where
  constructor residualFlow
  field
    Stage : Set
    Residual : Set
    next : Stage → Stage
    carries : Stage → Residual → Set
    Discharges : Stage → Residual → Set

open ResidualFlow public

record UnresolvedAt (flow : ResidualFlow)
    (stage : Stage flow) (residual : Residual flow) : Set₁ where
  constructor unresolvedAt
  field
    present : carries flow stage residual
    notDischarged : Discharges flow stage residual → ⊥

open UnresolvedAt public

record PropagatesOneStep (flow : ResidualFlow) : Set₁ where
  constructor propagatesOneStep
  field
    propagate :
      (stage : Stage flow) →
      (residual : Residual flow) →
      UnresolvedAt flow stage residual →
      carries flow (next flow stage) residual

open PropagatesOneStep public

unresolvedCannotSilentlyDisappear :
  (flow : ResidualFlow) →
  PropagatesOneStep flow →
  (stage : Stage flow) →
  (residual : Residual flow) →
  UnresolvedAt flow stage residual →
  (carries flow (next flow stage) residual → ⊥) → ⊥
unresolvedCannotSilentlyDisappear flow propagation stage residual unresolved absent =
  absent (propagate propagation stage residual unresolved)

record DischargeReceipt (flow : ResidualFlow)
    (stage : Stage flow) (residual : Residual flow) : Set₁ where
  constructor dischargeReceipt
  field
    dischargeWitness : Discharges flow stage residual

------------------------------------------------------------------------
-- Exact component plus explicit residual: not-all-or-nothing accounting.
------------------------------------------------------------------------

record ExactPlusResidual (Exact Residual : Set) : Set where
  constructor exactPlusResidual
  field
    exactPart : Exact
    residualPart : Residual

------------------------------------------------------------------------
-- Canonical finite pipeline.
------------------------------------------------------------------------

data DemoStage : Set where sourceStage translationStage theoremStage : DemoStage
data DemoResidual : Set where missingSemanticBridge : DemoResidual

nextDemo : DemoStage → DemoStage
nextDemo sourceStage = translationStage
nextDemo translationStage = theoremStage
nextDemo theoremStage = theoremStage

data DemoCarries : DemoStage → DemoResidual → Set where
  atSource : DemoCarries sourceStage missingSemanticBridge
  atTranslation : DemoCarries translationStage missingSemanticBridge
  atTheorem : DemoCarries theoremStage missingSemanticBridge

data DemoDischarges : DemoStage → DemoResidual → Set where

demoFlow : ResidualFlow
demoFlow = residualFlow DemoStage DemoResidual nextDemo DemoCarries DemoDischarges

demoPropagation : PropagatesOneStep demoFlow
demoPropagation = propagatesOneStep
  (λ
    { sourceStage missingSemanticBridge (unresolvedAt atSource _) → atTranslation
    ; translationStage missingSemanticBridge (unresolvedAt atTranslation _) → atTheorem
    ; theoremStage missingSemanticBridge (unresolvedAt atTheorem _) → atTheorem
    })

demoSourceUnresolved : UnresolvedAt demoFlow sourceStage missingSemanticBridge
demoSourceUnresolved = unresolvedAt atSource (λ ())

record ResidualPropagationBoundary : Set where
  constructor residualPropagationBoundary
  field
    downstreamPromotionSilentlyDischargesResidual : Bool
    downstreamPromotionSilentlyDischargesResidualIsFalse :
      downstreamPromotionSilentlyDischargesResidual ≡ false
    exactComponentMeansResidualIsZero : Bool
    exactComponentMeansResidualIsZeroIsFalse : exactComponentMeansResidualIsZero ≡ false
    unresolvedResidualMeansWholeConstructionFails : Bool
    unresolvedResidualMeansWholeConstructionFailsIsFalse :
      unresolvedResidualMeansWholeConstructionFails ≡ false
    explicitDischargeReceiptRequiredForClosure : Bool
    explicitDischargeReceiptRequiredForClosureIsTrue :
      explicitDischargeReceiptRequiredForClosure ≡ true

canonicalResidualPropagationBoundary : ResidualPropagationBoundary
canonicalResidualPropagationBoundary =
  residualPropagationBoundary false refl false refl false refl true refl
