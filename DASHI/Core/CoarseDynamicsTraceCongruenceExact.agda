module DASHI.Core.CoarseDynamicsTraceCongruenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability

------------------------------------------------------------------------
-- ONE-STEP COARSE COMMUTATION -> SAME-TRACE DYNAMIC SAFETY
--
-- CoarseDynamicsClosure already says that the declared deterministic fineStep
-- commutes with the coarse projection for one action.  A DependentActionSystem
-- may carry richer admissibility/postcondition evidence, so this theorem also
-- requires a witness that every admitted transition realizes that fineStep.
-- The conclusion is exactly the repository's existing DynamicConsumerSafety.
------------------------------------------------------------------------

coarseDynamicsClosurePromotesTraceSafety :
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
coarseDynamicsClosurePromotesTraceSafety
    {system = system}
    {fineStep = fineStep}
    geometry dynamics admissibleStepExact =
  Dynamic.dynamicConsumerSafety traceCongruence
  where
    traceCongruence :
      ∀ {actions left right leftAfter rightAfter} →
      Fibre.coarse geometry left ≡ Fibre.coarse geometry right →
      Reachability.Executes system actions left leftAfter →
      Reachability.Executes system actions right rightAfter →
      Fibre.coarse geometry leftAfter ≡ Fibre.coarse geometry rightAfter

    traceCongruence same Reachability.executesNil Reachability.executesNil = same

    traceCongruence
      {left = left} {right = right}
      same
      (Reachability.executesCons {action = action} leftAdmissible leftRest)
      (Reachability.executesCons rightAdmissible rightRest) =
        traceCongruence nextSame leftRest rightRest
      where
        nextSame :
          Fibre.coarse geometry (Dependency.after leftAdmissible)
          ≡
          Fibre.coarse geometry (Dependency.after rightAdmissible)
        nextSame =
          trans
            (cong (Fibre.coarse geometry)
              (admissibleStepExact left action leftAdmissible))
            (trans
              (Fibre.stepCommutes dynamics action left)
              (trans
                (cong (Fibre.coarseStep dynamics action) same)
                (trans
                  (sym (Fibre.stepCommutes dynamics action right))
                  (cong (Fibre.coarse geometry)
                    (sym (admissibleStepExact right action rightAdmissible))))))
