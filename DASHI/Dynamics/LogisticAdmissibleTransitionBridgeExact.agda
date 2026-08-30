module DASHI.Dynamics.LogisticAdmissibleTransitionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Dynamics.LogisticAdicStageCommutingSpine as Logistic

------------------------------------------------------------------------
-- LOGISTIC -> GENERIC ADMISSIBLE TRANSITION BRIDGE
------------------------------------------------------------------------

logisticInvariantRegionAsTransitionSystem :
  ∀ {Parameter State} →
  Logistic.LogisticInvariantRegion Parameter State →
  Transition.AdmissibleTransitionSystem
logisticInvariantRegionAsTransitionSystem {Parameter} {State} region =
  Transition.admissibleTransitionSystem
    State
    Parameter
    ⊤
    (λ _ parameter state → Logistic.admissibleParameter region parameter)
    (λ _ parameter state → Logistic.step region parameter state)
    (Logistic.contains region)
    (λ _ parameter state admissible inside →
      Logistic.preservesRegion region parameter state admissible inside)
    "logistic invariant-region admissibility"

logisticAdmittedStepRequiresAdmissibleParameter :
  ∀ {Parameter State}
    {region : Logistic.LogisticInvariantRegion Parameter State}
    {parameter : Parameter}
    {state : State} →
  Transition.AdmittedStep
    (logisticInvariantRegionAsTransitionSystem region)
    tt parameter state →
  Logistic.admissibleParameter region parameter
logisticAdmittedStepRequiresAdmissibleParameter =
  Transition.admittedStepHasEnablement

logisticAdmittedStepPreservesRegion :
  ∀ {Parameter State}
    {region : Logistic.LogisticInvariantRegion Parameter State}
    {parameter : Parameter}
    {state : State} →
  Transition.AdmittedStep
    (logisticInvariantRegionAsTransitionSystem region)
    tt parameter state →
  Logistic.contains region (Logistic.step region parameter state)
logisticAdmittedStepPreservesRegion =
  Transition.admittedStepPreservesInvariant

record LogisticAdmissibleTransitionBoundary : Set where
  constructor logisticAdmissibleTransitionBoundary
  field
    logisticInvariantRegionInstantiatesGenericTransitionGate : Bool
    logisticInvariantRegionInstantiatesGenericTransitionGateIsTrue :
      logisticInvariantRegionInstantiatesGenericTransitionGate ≡ true
    genericTransitionGateProvesContinuumChaos : Bool
    genericTransitionGateProvesContinuumChaosIsFalse :
      genericTransitionGateProvesContinuumChaos ≡ false
    genericTransitionGateIdentifiesRealAndPAdicDynamics : Bool
    genericTransitionGateIdentifiesRealAndPAdicDynamicsIsFalse :
      genericTransitionGateIdentifiesRealAndPAdicDynamics ≡ false

canonicalLogisticAdmissibleTransitionBoundary :
  LogisticAdmissibleTransitionBoundary
canonicalLogisticAdmissibleTransitionBoundary =
  logisticAdmissibleTransitionBoundary true refl false refl false refl
