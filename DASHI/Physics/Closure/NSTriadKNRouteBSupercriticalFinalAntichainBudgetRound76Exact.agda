module DASHI.Physics.Closure.NSTriadKNRouteBSupercriticalFinalAntichainBudgetRound76Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: P. A. P. Moran.
-- Title: "Additive functions of intervals and Hausdorff measure".
-- DOI: 10.1017/S0305004100022684.
--
-- Author: John E. Hutchinson.
-- Title: "Fractals and self-similarity".
-- DOI: 10.1512/iumj.1981.30.30055.
--
-- Author: J. D. Biggins.
-- Title: "Martingale convergence in the branching random walk".
-- DOI: 10.2307/3213258.
--
-- Author: Michael Hochman.
-- Title: "On self-similar sets with overlaps and inverse theorems for entropy".
-- DOI: 10.4007/annals.2014.180.2.7.
--
-- ROUND76 / ROUTE B: FINAL ANTICHAIN, NOT CROSS-GENERATION ADDITIVITY
--
-- Round75 proved for one physical-style supercritical antichain step
--
--   M_(j+1) = M_j + Delta_j,
--   Delta_j = sum_e mu_e^2 epsilon_e.
--
-- It also proved that sibling separation does not justify summing parent and
-- child charges across generations.  Route B does not need that stronger
-- property.  If the supercritical antichain mass grows, it is enough for ONE
-- final generation to exceed the finite physical budget.  Only the nodes in
-- that final antichain are then submitted to the existing Carleson ledger.
--
-- This file constructs that exact compiler:
--
--   chained supercritical steps
--     -> final mass = initial mass + cumulative weighted excess
--     -> final antichain floor mass above budget
--     -> contradiction with funding of that final antichain.
--
-- Therefore cross-generation charge orthogonality is not an obligation of the
-- supercritical Route B arithmetic.  The remaining physical PDE obligations
-- are narrower:
--
--   (1) source-native continuation from one critical antichain to the next;
--   (2) positive/non-summable cumulative weighted excess;
--   (3) actual charge funding of the selected FINAL antichain.
--
-- Biggins/Hochman are provenance and calibration only.  No probabilistic or
-- fractal theorem is imported into the finite deterministic proof below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNSupercriticalAntichainExcessRound75Exact as Super
import DASHI.Physics.Closure.NSTriadKNDeterministicIrregularSquaredCascadeRound74Exact as Cascade
import DASHI.Physics.Closure.NSTriadKNIrregularSquaredCascadeCarlesonRound74Exact as Funded
import DASHI.Physics.Closure.NSTriadKNPhysicalCarlesonFundingRound73Exact as Carleson

------------------------------------------------------------------------
-- Multi-generation telescoping on the antichain mass only.
------------------------------------------------------------------------

data SupercriticalAntichainHistory : ℚ → ℚ → Set where
  seed : (mass : ℚ) → SupercriticalAntichainHistory mass mass
  extend :
    ∀ {initial current}
      (history : SupercriticalAntichainHistory initial current)
      (step : Super.SupercriticalAntichainStep) →
    Super.parentMass step ≡ current →
    SupercriticalAntichainHistory initial (Super.childMass step)

cumulativeWeightedExcess :
  ∀ {initial final} →
  SupercriticalAntichainHistory initial final → ℚ
cumulativeWeightedExcess (seed mass) = 0ℚ
cumulativeWeightedExcess (extend history step alignment) =
  cumulativeWeightedExcess history + Super.excessMass step

historyFinalMassExact :
  ∀ {initial final}
    (history : SupercriticalAntichainHistory initial final) →
  final ≡ initial + cumulativeWeightedExcess history
historyFinalMassExact (seed mass) = solve (mass ∷ [])
historyFinalMassExact {initial} (extend {current = current} history step alignment) =
  let
    excess = Super.excessMass step
    previousExact : current ≡ initial + cumulativeWeightedExcess history
    previousExact = historyFinalMassExact history
  in
  trans
    (Super.antichainStepExactGrowth step)
    (trans
      (cong (_+ excess) alignment)
      (trans
        (cong (_+ excess) previousExact)
        (solve
          ( initial
          ∷ cumulativeWeightedExcess history
          ∷ excess
          ∷ []))))

historyCumulativeExcessAboveBudgetForcesFinalMassAboveBudget :
  ∀ {initial final budget}
    (history : SupercriticalAntichainHistory initial final) →
  budget < initial + cumulativeWeightedExcess history →
  budget < final
historyCumulativeExcessAboveBudgetForcesFinalMassAboveBudget
    history cumulativeAbove =
  subst
    (_ <_)
    (sym (historyFinalMassExact history))
    cumulativeAbove

------------------------------------------------------------------------
-- Fund ONLY one final antichain.  No parent/child charge sum is formed.
------------------------------------------------------------------------

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data PhysicallyFundedSupercriticalRows :
    List Cascade.SupercriticalSquaredPropagationRow → Set where
  fundedSuper[] : PhysicallyFundedSupercriticalRows []
  fundedSuper∷ :
    ∀ {row rows} →
    Funded.PhysicallyFundedLossChildren
      (Cascade.superParentAmplitude row)
      (Cascade.superChildLossWeights row) →
    PhysicallyFundedSupercriticalRows rows →
    PhysicallyFundedSupercriticalRows (row ∷ rows)

finalAntichainFundedNodes :
  ∀ {rows} →
  PhysicallyFundedSupercriticalRows rows →
  List Carleson.FundedNode
finalAntichainFundedNodes fundedSuper[] = []
finalAntichainFundedNodes (fundedSuper∷ children rest) =
  Funded.asFundedNodes children ++ finalAntichainFundedNodes rest

sumFloorsAppend :
  ∀ left right →
  Carleson.sumFloors (left ++ right)
  ≡ Carleson.sumFloors left + Carleson.sumFloors right
sumFloorsAppend [] right = refl
sumFloorsAppend (node ∷ rest) right =
  trans
    (cong (Carleson.floor node +_) (sumFloorsAppend rest right))
    (solve
      ( Carleson.floor node
      ∷ Carleson.sumFloors rest
      ∷ Carleson.sumFloors right
      ∷ []))

finalAntichainFundedFloorMassExact :
  ∀ {rows}
    (funding : PhysicallyFundedSupercriticalRows rows) →
  Carleson.sumFloors (finalAntichainFundedNodes funding)
  ≡ Super.superChildMass rows
finalAntichainFundedFloorMassExact fundedSuper[] = refl
finalAntichainFundedFloorMassExact
    (fundedSuper∷ {row = row} children rest) =
  trans
    (sumFloorsAppend
      (Funded.asFundedNodes children)
      (finalAntichainFundedNodes rest))
    (trans
      (cong₂ _+_
        (Funded.fundedChildrenFloorMassExact children)
        (finalAntichainFundedFloorMassExact rest))
      refl)

finalAntichainMassAboveBudgetRefutesFinalAntichainFunding :
  ∀ {rows budget}
    (funding : PhysicallyFundedSupercriticalRows rows) →
  budget < Super.superChildMass rows →
  ¬ Carleson.PhysicalCarlesonBudget
      (finalAntichainFundedNodes funding) budget
finalAntichainMassAboveBudgetRefutesFinalAntichainFunding
    funding above =
  Carleson.floorPrefixAboveBudgetRefutesCarlesonFunding
    (subst
      (λ floorMass → _ < floorMass)
      (sym (finalAntichainFundedFloorMassExact funding))
      above)

------------------------------------------------------------------------
-- The complete deterministic Route-B contradiction compiler.
------------------------------------------------------------------------

routeBFinalAntichainBudgetContradiction :
  ∀ {initial current budget}
    (history : SupercriticalAntichainHistory initial current)
    (step : Super.SupercriticalAntichainStep) →
  Super.parentMass step ≡ current →
  (funding : PhysicallyFundedSupercriticalRows (Super.rows step)) →
  budget
    < initial
      + (cumulativeWeightedExcess history + Super.excessMass step) →
  ¬ Carleson.PhysicalCarlesonBudget
      (finalAntichainFundedNodes funding) budget
routeBFinalAntichainBudgetContradiction
    {initial} history step alignment funding cumulativeAbove =
  let
    extended = extend history step alignment

    finalAbove : budget < Super.childMass step
    finalAbove =
      historyCumulativeExcessAboveBudgetForcesFinalMassAboveBudget
        extended cumulativeAbove

    physicalFinalAbove : budget < Super.superChildMass (Super.rows step)
    physicalFinalAbove =
      subst
        (budget <_)
        (Super.childMassExact step)
        finalAbove
  in
  finalAntichainMassAboveBudgetRefutesFinalAntichainFunding
    funding physicalFinalAbove

round76RouteBNeedsNoCrossGenerationChargeAdditivity : Bool
round76RouteBNeedsNoCrossGenerationChargeAdditivity = true

round76CumulativeWeightedExcessTelescopesExactly : Bool
round76CumulativeWeightedExcessTelescopesExactly = true

round76FinalAntichainAloneCanContradictFiniteBudget : Bool
round76FinalAntichainAloneCanContradictFiniteBudget = true

round76PhysicalSupercriticalExcessProducerConstructed : Bool
round76PhysicalSupercriticalExcessProducerConstructed = false

round76PhysicalFinalAntichainChargeProducerConstructed : Bool
round76PhysicalFinalAntichainChargeProducerConstructed = false

round76FinalAntichainAloneCanContradictFiniteBudgetIsTrue :
  round76FinalAntichainAloneCanContradictFiniteBudget ≡ true
round76FinalAntichainAloneCanContradictFiniteBudgetIsTrue = refl
