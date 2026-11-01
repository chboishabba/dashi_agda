module DASHI.Biology.Physical.GraphGeneratingGoalControllerExact where

------------------------------------------------------------------------
-- Explicit closed-loop factorization requested by the attachment:
--
--   Sense -> Goal -> Error -> Policy -> LocalAction -> GraphRewrite.
--
-- The finite target is an integrated hand-like tissue graph.  This theorem is
-- about factorization and corrective reachability, not a calibrated limb model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.DynamicTissueGraphRewriteExact as Graph

record Observation : Set where
  constructor observation
  field
    hasJunction : Bool
    isDifferentiated : Bool
    isAttached : Bool

open Observation public

sense : Graph.TissueGraphState → Observation
sense x = observation
  (Graph.junctionPresent x)
  (Graph.differentiated x)
  (Graph.attachedToBody x)

record Goal : Set where
  constructor goal
  field
    needJunction : Bool
    needDifferentiation : Bool
    needAttachment : Bool

open Goal public

integratedHandGoal : Goal
integratedHandGoal = goal true true true

record Error : Set where
  constructor error
  field
    junctionMissing : Bool
    differentiationMissing : Bool
    attachmentMissing : Bool

open Error public

not : Bool → Bool
not false = true
not true = false

and : Bool → Bool → Bool
and true true = true
and _ _ = false

computeError : Observation → Goal → Error
computeError o g = error
  (and (needJunction g) (not (hasJunction o)))
  (and (needDifferentiation g) (not (isDifferentiated o)))
  (and (needAttachment g) (not (isAttached o)))

record PolicyAction : Set where
  constructor policyAction
  field
    connectNow : Bool
    differentiateNow : Bool
    attachNow : Bool

open PolicyAction public

policy : Error → PolicyAction
policy e = policyAction
  (junctionMissing e)
  (differentiationMissing e)
  (attachmentMissing e)

executeOne : Bool → Graph.CellAction → Graph.TissueGraphState → Graph.TissueGraphState
executeOne false action x = x
executeOne true action x = Graph.rewrite action x

localAction : PolicyAction → Graph.TissueGraphState → Graph.TissueGraphState
localAction a x =
  executeOne (attachNow a) Graph.attach
    (executeOne (differentiateNow a) Graph.differentiate
      (executeOne (connectNow a) Graph.connect x))

graphRewrite : Graph.TissueGraphState → Graph.TissueGraphState
graphRewrite = λ x → x

closedLoopStep : Goal → Graph.TissueGraphState → Graph.TissueGraphState
closedLoopStep g x =
  graphRewrite
    (localAction
      (policy (computeError (sense x) g))
      x)

closedLoopFactorises :
  (g : Goal) (x : Graph.TissueGraphState) →
  closedLoopStep g x ≡
    graphRewrite
      (localAction
        (policy (computeError (sense x) g))
        x)
closedLoopFactorises g x = refl

------------------------------------------------------------------------
-- Corrective theorem for the integrated graph target.
------------------------------------------------------------------------

closedLoopHitsIntegratedConstraint :
  (x : Graph.TissueGraphState) →
  Graph.IntegratedOrganConstraint (closedLoopStep integratedHandGoal x)
closedLoopHitsIntegratedConstraint
  (Graph.tissueGraphState n false p false false) =
  Graph.integratedOrganConstraint refl refl refl
closedLoopHitsIntegratedConstraint
  (Graph.tissueGraphState n false p false true) =
  Graph.integratedOrganConstraint refl refl refl
closedLoopHitsIntegratedConstraint
  (Graph.tissueGraphState n false p true false) =
  Graph.integratedOrganConstraint refl refl refl
closedLoopHitsIntegratedConstraint
  (Graph.tissueGraphState n false p true true) =
  Graph.integratedOrganConstraint refl refl refl
closedLoopHitsIntegratedConstraint
  (Graph.tissueGraphState n true p false false) =
  Graph.integratedOrganConstraint refl refl refl
closedLoopHitsIntegratedConstraint
  (Graph.tissueGraphState n true p false true) =
  Graph.integratedOrganConstraint refl refl refl
closedLoopHitsIntegratedConstraint
  (Graph.tissueGraphState n true p true false) =
  Graph.integratedOrganConstraint refl refl refl
closedLoopHitsIntegratedConstraint
  (Graph.tissueGraphState n true p true true) =
  Graph.integratedOrganConstraint refl refl refl

closedLoopFixesIntegratedState :
  (n : Nat) (p : Bool) →
  closedLoopStep integratedHandGoal
    (Graph.tissueGraphState n true p true true)
  ≡ Graph.tissueGraphState n true p true true
closedLoopFixesIntegratedState n p = refl

-- The controller delegates: it computes only missing high-level constraints;
-- the local rewrite layer performs the graph/state corrections.
