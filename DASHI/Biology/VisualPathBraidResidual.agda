module DASHI.Biology.VisualPathBraidResidual where

open import DASHI.Core.Prelude

import DASHI.Biology.ProductiveTransformCoherence as Coherence
import DASHI.Biology.StateDependentMultiplexTransducer as Stateful
import DASHI.Biology.QuantitativeCompositionalDefect as Defect

------------------------------------------------------------------------
-- Path-history / braid residual for visual transforms.
--
-- Two histories contain the same transform components with different order.
-- Their endpoints differ, giving an exact order residual and a finite bridge
-- from the existing braid-oriented formalism to psychedelic visual dynamics.

data VisualTransformComponent : Set where
  completionComponent : VisualTransformComponent
  inhibitionComponent : VisualTransformComponent

data TwoStepHistory : Set where
  inhibitionThenCompletion : TwoStepHistory
  completionThenInhibition : TwoStepHistory

firstComponent : TwoStepHistory → VisualTransformComponent
firstComponent inhibitionThenCompletion = inhibitionComponent
firstComponent completionThenInhibition = completionComponent

secondComponent : TwoStepHistory → VisualTransformComponent
secondComponent inhibitionThenCompletion = completionComponent
secondComponent completionThenInhibition = inhibitionComponent

executeHistory : TwoStepHistory → Bool → Bool
executeHistory inhibitionThenCompletion x =
  Coherence.setTrue (Stateful.boolNot x)
executeHistory completionThenInhibition x =
  Stateful.boolNot (Coherence.setTrue x)

inhibitionThenCompletionEndsTrue :
  executeHistory inhibitionThenCompletion false ≡ true
inhibitionThenCompletionEndsTrue = refl

completionThenInhibitionEndsFalse :
  executeHistory completionThenInhibition false ≡ false
completionThenInhibitionEndsFalse = refl

sameComponentsDifferentOrder :
  firstComponent inhibitionThenCompletion
  ≡
  secondComponent completionThenInhibition
  ×
  secondComponent inhibitionThenCompletion
  ≡
  firstComponent completionThenInhibition
sameComponentsDifferentOrder = refl , refl

historyEndpointsDiffer :
  executeHistory inhibitionThenCompletion false
  ≡
  executeHistory completionThenInhibition false
  →
  ⊥
historyEndpointsDiffer ()

historyResidual : TwoStepHistory → TwoStepHistory → Bool → Nat
historyResidual first second input =
  Defect.boolDistance
    (executeHistory first input)
    (executeHistory second input)

canonicalHistoryResidualIsOne :
  historyResidual
    inhibitionThenCompletion
    completionThenInhibition
    false
  ≡
  1
canonicalHistoryResidualIsOne = refl

------------------------------------------------------------------------
-- Initial condition and path order are independent coordinates.

data InitialVisualState : Set where
  lowActivationInitial : InitialVisualState
  highActivationInitial : InitialVisualState

initialCarrier : InitialVisualState → Bool
initialCarrier lowActivationInitial = false
initialCarrier highActivationInitial = true

pathOutcome : TwoStepHistory → InitialVisualState → Bool
pathOutcome history state =
  executeHistory history (initialCarrier state)

orderStillDominatesAtHighInitialState :
  pathOutcome inhibitionThenCompletion highActivationInitial
  ≡
  pathOutcome completionThenInhibition highActivationInitial
  →
  ⊥
orderStillDominatesAtHighInitialState ()

record VisualBraidWitness : Set where
  constructor visualBraidWitness
  field
    firstHistory : TwoStepHistory
    secondHistory : TwoStepHistory
    sameComponentMultiset :
      firstComponent firstHistory ≡ secondComponent secondHistory
      ×
      secondComponent firstHistory ≡ firstComponent secondHistory
    endpointResidual :
      historyResidual firstHistory secondHistory false ≡ 1

open VisualBraidWitness public

canonicalVisualBraidWitness : VisualBraidWitness
canonicalVisualBraidWitness =
  visualBraidWitness
    inhibitionThenCompletion
    completionThenInhibition
    sameComponentsDifferentOrder
    canonicalHistoryResidualIsOne

record VisualPathBoundary : Set where
  constructor visualPathBoundary
  field
    sameComponentsForceSameEndpoint : Bool
    sameComponentsForceSameEndpointIsFalse :
      sameComponentsForceSameEndpoint ≡ false

    residualDiagnosesPersonalHistory : Bool
    residualDiagnosesPersonalHistoryIsFalse :
      residualDiagnosesPersonalHistory ≡ false

open VisualPathBoundary public

canonicalVisualPathBoundary : VisualPathBoundary
canonicalVisualPathBoundary =
  visualPathBoundary false refl false refl
