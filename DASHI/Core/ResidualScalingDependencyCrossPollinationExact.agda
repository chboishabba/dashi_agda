module DASHI.Core.ResidualScalingDependencyCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ResidualObserverDependencyExact as Dependency
import DASHI.Core.ResidualScalingLawEscapeExact as Scaling

------------------------------------------------------------------------
-- RESIDUAL-SCALING / RESIDUAL-DEPENDENCY CROSS-POLLINATION
--
-- A residual scaling witness can be re-read as hidden residual dependency:
-- the same coarse collision that blocks a one-coordinate scaling law also
-- supplies a strict residual refinement for any action-indexed consumer that
-- reads the residual coordinate as its dependency code.
------------------------------------------------------------------------

residualAsDependency :
  ∀ {State Action Residual : Set} →
  Observer.Observer State Residual →
  Dependency.ResidualDependencyObserver State Action ⊤ Residual
residualAsDependency residual = record
  { Influences = λ _ _ _ _ → ⊤
  ; dependencyCode = λ state _ → residual state
  }

scalingWitnessGivesHiddenResidualDependency :
  ∀ {State Action Coarse Residual Target : Set}
    {coarse : Observer.Observer State Coarse}
    {residual : Observer.Observer State Residual}
    {target : Observer.Observer State Target}
    (action : Action) →
  Scaling.ResidualScalingWitness coarse residual target →
  Dependency.HiddenResidualDependency
    (residualAsDependency residual)
    coarse
    action
scalingWitnessGivesHiddenResidualDependency action witness =
  Dependency.hiddenResidualDependency
    (Scaling.left witness)
    (Scaling.right witness)
    (Scaling.sameCoarse witness)
    (Scaling.residualSeparates witness)

scalingWitnessBlocksResidualDependencyDescent :
  ∀ {State Action Coarse Residual Target : Set}
    {coarse : Observer.Observer State Coarse}
    {residual : Observer.Observer State Residual}
    {target : Observer.Observer State Target}
    (action : Action) →
  Scaling.ResidualScalingWitness coarse residual target →
  Dependency.DependencyCodeDescendsAt
    (residualAsDependency residual)
    coarse
    action →
  ⊥
scalingWitnessBlocksResidualDependencyDescent action witness =
  Dependency.hiddenResidualDependencyBlocksDescent
    (scalingWitnessGivesHiddenResidualDependency action witness)

------------------------------------------------------------------------
-- BIDI meaning:
--
-- forward  : a scaling witness produces a hidden residual-dependency witness;
-- reverse  : a consumer claim that the residual dependency descends through
--            the coarse chart is rejected by the same separating pair.
--
-- This bridge does not identify target separation with causal influence.  The
-- action-indexed Influences field above is deliberately trivial because the
-- theorem being transported is informational non-descent, not causal effect.
------------------------------------------------------------------------

record ScalingDependencyBoundary : Set where
  constructor scaling-dependency-boundary
  field
    scalingWitnessCanInstantiateResidualDependency : Bool
    scalingWitnessCanInstantiateResidualDependencyIsTrue :
      scalingWitnessCanInstantiateResidualDependency ≡ true

    residualNonDescentTransported : Bool
    residualNonDescentTransportedIsTrue :
      residualNonDescentTransported ≡ true

    targetSeparationAutomaticallyMeansCausalInfluence : Bool
    targetSeparationAutomaticallyMeansCausalInfluenceIsFalse :
      targetSeparationAutomaticallyMeansCausalInfluence ≡ false

canonicalScalingDependencyBoundary : ScalingDependencyBoundary
canonicalScalingDependencyBoundary =
  scaling-dependency-boundary true refl true refl false refl
