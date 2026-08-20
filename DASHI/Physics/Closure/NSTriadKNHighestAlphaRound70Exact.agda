module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound70Exact where

------------------------------------------------------------------------
-- ROUND 70 HIGHEST-ALPHA CUTSET
--
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
-- ROUND70 RESULT
--
-- Round69 isolated the non-circular concentration route.  Round70 now audits
-- its quantitative viability BEFORE attempting a Carleman implementation.
--
-- CONSTRUCTED:
--
-- 1. Scale-dependent funding.  If event i has a literal lower charge floor
--    mu_i, then
--
--        sum_i mu_i <= total physical charge <= E.
--
--    A scale-independent mu is sufficient but NOT necessary.
--
-- 2. Exact barrier criterion.  The propagated floor family only needs to
--    outrun every finite budget: for every E there must exist a FINITE prefix N
--    with E < sum_{i<N} mu_i.  Such a prefix contradicts one-budget funding.
--
-- 3. Exact summability no-go.  If all floors are nonnegative and their finite
--    cumulative sum is <=E, there is an explicit compatible event ledger with
--    charge_i=mu_i.  The funding argument alone then has no contradiction.
--
-- 4. Concrete dyadic falsifier by cross-pollinating Round62's exact geometric
--    summation theorem.  Floors 1,1/2,1/4,... have every finite partial sum <=2,
--    and every finite propagation prefix is explicitly fundable by E=2.
--    Therefore arbitrarily many distinct events with dyadically degrading
--    guaranteed charge do NOT establish the invariant Xi barrier.
--
-- 5. Block-index separation no-go.  The current canonical C1 carrier indexes
--    critical blocks by Nat but contains no support map.  A constant support
--    assignment is valid, so n!=m cannot be treated as physical/frequency
--    disjointness without a new same-object theorem.
--
-- CONSEQUENCE:
--
-- The decisive propagation theorem is now quantitatively precise.  It need not
-- preserve one uniform c, but it MUST produce physical charge floors whose
-- cumulative finite-prefix mass outruns the one finite energy/enstrophy budget,
-- or provide a different contradiction.  Carleman iteration is acceptable only
-- if its losses satisfy this criterion.  A direct dyadic telescoping/separation
-- mechanism would be preferable if it can be proved on the literal trajectory.
--
-- NEW SHORTEST FRONTIER:
--
-- A. selected Galerkin trajectory;
-- B. literal localized trajectory identity emitting the Round62 structured PDE
--    atoms;
-- C. critical amplification -> structured concentration with explicit physical
--    charge floor mu_0, without Xi<=K;
-- D. physical propagation/separation theorem producing a floor family that
--    outruns every finite budget (uniform c is not required);
-- E. combine D with Round70 funding to obtain the invariant Xi barrier;
-- F. then finish the already-isolated Gram/HH-bad/data/kernel/continuum/gate
--    closures.
--
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound69Exact
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding
import DASHI.Physics.Closure.NSTriadKNPropagationFloorBarrierRound70Exact as Barrier
import DASHI.Physics.Closure.NSTriadKNDyadicPropagationFundingNoGoRound70Exact as DyadicNoGo
import DASHI.Physics.Closure.NSTriadKNCriticalBlockSupportSeparationNoGoRound70Exact as SupportNoGo

round70ScaleDependentFundingConstructed : Bool
round70ScaleDependentFundingConstructed =
  Funding.round70ScaleDependentFundingCriterionConstructed

round70BudgetOutrunningBarrierCriterionConstructed : Bool
round70BudgetOutrunningBarrierCriterionConstructed =
  Barrier.round70BudgetOutrunningIsExactBarrierCriterion

round70UniformPropagationChargeNecessary : Bool
round70UniformPropagationChargeNecessary =
  Barrier.round70UniformScaleIndependentChargeNecessary

round70SummablePropagationFundingNoGoConstructed : Bool
round70SummablePropagationFundingNoGoConstructed =
  Funding.round70SummableFloorFundingNoGoConstructed

round70DyadicPropagationFundingFalsified : Bool
round70DyadicPropagationFundingFalsified =
  DyadicNoGo.round70DyadicPropagationFundingContradictionFalsified

round70BlockIndexSupportSeparationNoGoConstructed : Bool
round70BlockIndexSupportSeparationNoGoConstructed =
  SupportNoGo.round70BlockSupportSeparationNeedsPhysicalProducer

-- Genuine remaining physical producers on the decisive path.
round70SelectedGalerkinTrajectoryConstructed : Bool
round70SelectedGalerkinTrajectoryConstructed = false

round70LiteralTrajectoryEmitsStructuredAtoms : Bool
round70LiteralTrajectoryEmitsStructuredAtoms = false

round70CriticalAmplificationForcesStructuredConcentration : Bool
round70CriticalAmplificationForcesStructuredConcentration = false

round70PhysicalPropagationFloorsOutrunEveryFiniteBudget : Bool
round70PhysicalPropagationFloorsOutrunEveryFiniteBudget = false

round70CriticalRatioBarrierConstructed : Bool
round70CriticalRatioBarrierConstructed = false

round70ClayPromotion : Bool
round70ClayPromotion = false

round70ScaleDependentFundingConstructedIsTrue :
  round70ScaleDependentFundingConstructed ≡ true
round70ScaleDependentFundingConstructedIsTrue = refl

round70BudgetOutrunningBarrierCriterionConstructedIsTrue :
  round70BudgetOutrunningBarrierCriterionConstructed ≡ true
round70BudgetOutrunningBarrierCriterionConstructedIsTrue = refl

round70UniformPropagationChargeNecessaryIsFalse :
  round70UniformPropagationChargeNecessary ≡ false
round70UniformPropagationChargeNecessaryIsFalse = refl

round70SummablePropagationFundingNoGoConstructedIsTrue :
  round70SummablePropagationFundingNoGoConstructed ≡ true
round70SummablePropagationFundingNoGoConstructedIsTrue = refl

round70DyadicPropagationFundingFalsifiedIsTrue :
  round70DyadicPropagationFundingFalsified ≡ true
round70DyadicPropagationFundingFalsifiedIsTrue = refl

round70BlockIndexSupportSeparationNoGoConstructedIsTrue :
  round70BlockIndexSupportSeparationNoGoConstructed ≡ true
round70BlockIndexSupportSeparationNoGoConstructedIsTrue = refl

round70CriticalAmplificationForcesStructuredConcentrationIsFalse :
  round70CriticalAmplificationForcesStructuredConcentration ≡ false
round70CriticalAmplificationForcesStructuredConcentrationIsFalse = refl

round70PhysicalPropagationFloorsOutrunEveryFiniteBudgetIsFalse :
  round70PhysicalPropagationFloorsOutrunEveryFiniteBudget ≡ false
round70PhysicalPropagationFloorsOutrunEveryFiniteBudgetIsFalse = refl

round70CriticalRatioBarrierConstructedIsFalse :
  round70CriticalRatioBarrierConstructed ≡ false
round70CriticalRatioBarrierConstructedIsFalse = refl

round70ClayPromotionIsFalse : round70ClayPromotion ≡ false
round70ClayPromotionIsFalse = refl
