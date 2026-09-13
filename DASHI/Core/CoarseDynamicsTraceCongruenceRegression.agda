module DASHI.Core.CoarseDynamicsTraceCongruenceRegression where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.CoarseDynamicsTraceCongruenceExact as Bridge

------------------------------------------------------------------------
-- RED/GREEN CONTRACT
------------------------------------------------------------------------

coarseDynamicsClosurePromotesTraceSafetySurface :
  ∀ {FineState Action : Set}
    {system : Dependency.DependentActionSystem FineState Action}
    {fineStep : Action → FineState → FineState}
    (geometry : Fibre.CoarseFineReopening FineState) →
  Fibre.CoarseDynamicsClosure geometry fineStep →
  ((before : FineState) →
    (action : Action) →
    (admissible : Dependency.AdmissibleAction system before action) →
    Dependency.after admissible ≡ fineStep action before) →
  Dynamic.DynamicConsumerSafety system (Fibre.coarse geometry)
coarseDynamicsClosurePromotesTraceSafetySurface =
  Bridge.coarseDynamicsClosurePromotesTraceSafety
