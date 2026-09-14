module DASHI.Core.ConsumerResidualRepairCrosswalkExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Residual

------------------------------------------------------------------------
-- CONSUMER RESIDUAL REPAIR CROSSWALK
--
-- The older consumer-indexed residual owner and the canonical descent/repair
-- spine carry the same collision and joint-sufficiency information.  Preserve
-- the richer residual terminology, but make the exact translation explicit so
-- the canonical repair theorem can be reused rather than reproved.
------------------------------------------------------------------------

residualCollisionToNonDescent :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Residual.ConsumerRelevantCollision observe consumer →
  Descent.ConsumerNonDescentWitness observe consumer
residualCollisionToNonDescent collision =
  Descent.consumerNonDescentWitness
    (Residual.left collision)
    (Residual.right collision)
    (Residual.sameSurface collision)
    (Residual.differentOutcome collision)

nonDescentToResidualCollision :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerNonDescentWitness observe consumer →
  Residual.ConsumerRelevantCollision observe consumer
nonDescentToResidualCollision witness =
  Residual.consumer-relevant-collision
    (Descent.left witness)
    (Descent.right witness)
    (Descent.sameSurface witness)
    (Descent.differentOutcome witness)

residualSufficientToCanonical :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Residual.ConsumerSufficient observe consumer →
  Descent.ConsumerSufficient observe consumer
residualSufficientToCanonical sufficient = sufficient

canonicalSufficientToResidual :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerSufficient observe consumer →
  Residual.ConsumerSufficient observe consumer
canonicalSufficientToResidual sufficient = sufficient

residualRepairToCanonicalRepair :
  ∀ {State Coarse Fine Outcome : Set}
    {coarse : State → Coarse}
    {fine : State → Fine}
    {consumer : State → Outcome} →
  Residual.ResidualRepair coarse fine consumer →
  Repair.RefinementRepairs coarse fine consumer
residualRepairToCanonicalRepair repair =
  Residual.jointSufficient repair

canonicalRepairToResidualRepair :
  ∀ {State Coarse Fine Outcome : Set}
    {coarse : State → Coarse}
    {fine : State → Fine}
    {consumer : State → Outcome} →
  Repair.RefinementRepairs coarse fine consumer →
  Residual.ResidualRepair coarse fine consumer
canonicalRepairToResidualRepair repaired =
  Residual.residual-repair repaired

residualMustSeparateViaCanonicalRepair :
  ∀ {State Coarse Fine Outcome : Set}
    {coarse : State → Coarse}
    {fine : State → Fine}
    {consumer : State → Outcome} →
  (collision : Residual.ConsumerRelevantCollision coarse consumer) →
  (repair : Residual.ResidualRepair coarse fine consumer) →
  fine (Residual.left collision) ≡ fine (Residual.right collision) → ⊥
residualMustSeparateViaCanonicalRepair collision repair =
  Repair.refinementRepairSeparatesWitness
    (residualCollisionToNonDescent collision)
    (residualRepairToCanonicalRepair repair)
