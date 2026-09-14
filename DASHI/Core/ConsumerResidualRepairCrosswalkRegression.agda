module DASHI.Core.ConsumerResidualRepairCrosswalkRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Residual
import DASHI.Core.ConsumerResidualRepairCrosswalkExact as Crosswalk

collisionToCanonicalWitness :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Residual.ConsumerRelevantCollision observe consumer →
  Descent.ConsumerNonDescentWitness observe consumer
collisionToCanonicalWitness = Crosswalk.residualCollisionToNonDescent

canonicalWitnessToCollision :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerNonDescentWitness observe consumer →
  Residual.ConsumerRelevantCollision observe consumer
canonicalWitnessToCollision = Crosswalk.nonDescentToResidualCollision

residualRepairToCanonicalRepair :
  ∀ {State Coarse Fine Outcome : Set}
    {coarse : State → Coarse}
    {fine : State → Fine}
    {consumer : State → Outcome} →
  Residual.ResidualRepair coarse fine consumer →
  Repair.RefinementRepairs coarse fine consumer
residualRepairToCanonicalRepair = Crosswalk.residualRepairToCanonicalRepair

canonicalRepairToResidualRepair :
  ∀ {State Coarse Fine Outcome : Set}
    {coarse : State → Coarse}
    {fine : State → Fine}
    {consumer : State → Outcome} →
  Repair.RefinementRepairs coarse fine consumer →
  Residual.ResidualRepair coarse fine consumer
canonicalRepairToResidualRepair = Crosswalk.canonicalRepairToResidualRepair
