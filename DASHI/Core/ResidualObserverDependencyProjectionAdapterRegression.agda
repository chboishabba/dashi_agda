module DASHI.Core.ResidualObserverDependencyProjectionAdapterRegression where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Core.ResidualObserverDependencyExact as Residual

hiddenDependencyProjectsToCanonicalCollision :
  ∀ {State Action Index Code Coarse : Set}
    {dependency : Residual.ResidualDependencyObserver State Action Index Code}
    {coarse : State → Coarse}
    {action : Action} →
  Residual.HiddenResidualDependency dependency coarse action →
  Calculus.ProjectionCollision
    coarse
    (Residual.residualDependencyAt dependency action)
hiddenDependencyProjectsToCanonicalCollision =
  Residual.hiddenResidualDependencyProjectionCollision

hiddenDependencyRefutesCoarseFactorisation :
  ∀ {State Action Index Code Coarse : Set}
    {dependency : Residual.ResidualDependencyObserver State Action Index Code}
    {coarse : State → Coarse}
    {action : Action} →
  Residual.HiddenResidualDependency dependency coarse action →
  (coarseCode : Coarse → Code) →
  ((state : State) →
    Residual.residualDependencyAt dependency action state
    ≡ coarseCode (coarse state)) →
  ⊥
hiddenDependencyRefutesCoarseFactorisation =
  Residual.hiddenResidualDependencyRefutesCoarseFactorisation
