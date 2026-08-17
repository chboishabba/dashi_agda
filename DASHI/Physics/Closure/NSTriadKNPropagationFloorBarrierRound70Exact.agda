module DASHI.Physics.Closure.NSTriadKNPropagationFloorBarrierRound70Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Authors: Ruilin Hu; Phuoc-Tai Nguyen; Quoc-Hung Nguyen; Ping Zhang.
-- Title: "Quantitative bounds for bounded solutions to the Navier-Stokes
-- equations in endpoint critical Besov spaces".
-- arXiv DOI: 10.48550/arXiv.2411.06483.
--
-- ROUND 70 / EXACT BARRIER INTERFACE
--
-- Scale-uniform concentration strength is stronger than necessary.  What the
-- finite-funding contradiction actually consumes is a family of finite
-- propagated event prefixes whose cumulative charge floors outrun EVERY finite
-- physical budget.
--
--     for every E, there exists N with E < sum_{j<N} floor_j.
--
-- Once a physical propagation theorem supplies such a family and identifies
-- every prefix with distinct events charged to one budget E, the Round70
-- scale-dependent funding theorem immediately contradicts funding of that
-- prefix.  No Carleman constant, asymptotic notation or infinite-series
-- theorem is hidden in this arithmetic layer.
--
-- Conversely, Round70's summable-floor model proves why merely producing
-- infinitely many events is insufficient: if all finite prefixes remain below
-- E, there is an explicit ledger with charge exactly equal to each floor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Rational.Base using (ℚ; _<_)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNFiniteDisjointConcentrationBudgetRound69Exact as R69
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding

record PropagationFloorFamily : Set where
  field
    floorsAt : Nat → List ℚ
    floorsNonnegativeAt : ∀ n → Funding.AllFloorsNonnegative (floorsAt n)

    -- Exact non-summability / budget-outrunning condition needed by the
    -- contradiction.  This deliberately quantifies only over finite prefixes.
    outrunsEveryFiniteBudget :
      (energy : ℚ) →
      Σ Nat (λ n → energy < Funding.sumFloors (floorsAt n))

open PropagationFloorFamily public

record PhysicalPropagationFunding
    (family : PropagationFloorFamily)
    (energy : ℚ) : Set where
  field
    eventsAt : Nat → List R69.ConcentrationEvent
    fundedAt : ∀ n →
      Funding.ScaleDependentConcentrationBudget
        energy (floorsAt family n) (eventsAt n)

open PhysicalPropagationFunding public

-- No one finite physical budget can fund all prefixes of a family whose
-- cumulative required charge outruns every finite budget.
propagationFloorFamilyContradictsUniformFunding :
  (family : PropagationFloorFamily) →
  (energy : ℚ) →
  ¬ PhysicalPropagationFunding family energy
propagationFloorFamilyContradictsUniformFunding family energy funding
  with outrunsEveryFiniteBudget family energy
... | n , excess =
  Funding.prefixFloorAboveEnergyContradictsBudget
    excess (fundedAt funding n)

-- Pointwise version useful when the PDE layer has already produced a specific
-- bad prefix: no need to construct the entire family before obtaining the
-- contradiction.
oneBadPrefixContradictsFunding :
  (family : PropagationFloorFamily) →
  (energy : ℚ) →
  (n : Nat) →
  energy < Funding.sumFloors (floorsAt family n) →
  (events : List R69.ConcentrationEvent) →
  ¬ Funding.ScaleDependentConcentrationBudget
      energy (floorsAt family n) events
oneBadPrefixContradictsFunding family energy n excess events =
  Funding.prefixFloorAboveEnergyContradictsBudget excess

round70BudgetOutrunningIsExactBarrierCriterion : Bool
round70BudgetOutrunningIsExactBarrierCriterion = true

round70UniformScaleIndependentChargeNecessary : Bool
round70UniformScaleIndependentChargeNecessary = false

round70PhysicalPropagationFloorFamilyConstructed : Bool
round70PhysicalPropagationFloorFamilyConstructed = false

round70BudgetOutrunningIsExactBarrierCriterionIsTrue :
  round70BudgetOutrunningIsExactBarrierCriterion ≡ true
round70BudgetOutrunningIsExactBarrierCriterionIsTrue = refl

round70UniformScaleIndependentChargeNecessaryIsFalse :
  round70UniformScaleIndependentChargeNecessary ≡ false
round70UniformScaleIndependentChargeNecessaryIsFalse = refl

round70PhysicalPropagationFloorFamilyConstructedIsFalse :
  round70PhysicalPropagationFloorFamilyConstructed ≡ false
round70PhysicalPropagationFloorFamilyConstructedIsFalse = refl
