module DASHI.Papers.NavierStokes.TheoremInterfaceRound70Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND70 DELTA
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
-- Round70 sharpens the quantitative condition needed after Round69's
-- amplification -> concentration discriminator.
--
-- A fixed scale-independent concentration floor is NOT required.  For literal
-- propagated floors mu_i, finite energy only gives
--
--     sum_i mu_i <= E.
--
-- Thus the exact contradiction criterion is that finite propagated prefixes
-- eventually outrun every finite physical budget.  Round70 constructs this
-- scale-dependent funding theorem and the corresponding barrier interface.
--
-- It also proves two falsifiers:
--
-- * summable floors admit an explicit charge ledger and therefore cannot yield
--   a funding contradiction by themselves;
-- * specifically, dyadic floors 1,1/2,1/4,... are all funded by E=2, using the
--   exact geometric summation already proved in Round62;
-- * the Nat critical-block index alone does not imply distinct physical
--   supports; a constant support assignment is structurally valid.
--
-- Therefore the remaining propagation theorem must prove a same-object family
-- of distinct physical events whose cumulative guaranteed charges outrun the
-- finite budget, or use a fundamentally different contradiction.  Clay
-- promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound69Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound70Exact as R70

round70PaperScaleDependentFundingConstructed : Bool
round70PaperScaleDependentFundingConstructed =
  R70.round70ScaleDependentFundingConstructed

round70PaperBudgetOutrunningCriterionConstructed : Bool
round70PaperBudgetOutrunningCriterionConstructed =
  R70.round70BudgetOutrunningBarrierCriterionConstructed

round70PaperUniformPropagationChargeNecessary : Bool
round70PaperUniformPropagationChargeNecessary =
  R70.round70UniformPropagationChargeNecessary

round70PaperSummableFloorNoGoConstructed : Bool
round70PaperSummableFloorNoGoConstructed =
  R70.round70SummablePropagationFundingNoGoConstructed

round70PaperDyadicPropagationFundingFalsified : Bool
round70PaperDyadicPropagationFundingFalsified =
  R70.round70DyadicPropagationFundingFalsified

round70PaperBlockSupportSeparationNoGoConstructed : Bool
round70PaperBlockSupportSeparationNoGoConstructed =
  R70.round70BlockIndexSupportSeparationNoGoConstructed

round70PaperCriticalAmplificationForcesStructuredConcentration : Bool
round70PaperCriticalAmplificationForcesStructuredConcentration =
  R70.round70CriticalAmplificationForcesStructuredConcentration

round70PaperPhysicalPropagationOutrunsBudget : Bool
round70PaperPhysicalPropagationOutrunsBudget =
  R70.round70PhysicalPropagationFloorsOutrunEveryFiniteBudget

round70PaperCriticalRatioBarrier : Bool
round70PaperCriticalRatioBarrier = R70.round70CriticalRatioBarrierConstructed

round70PaperClayPromotion : Bool
round70PaperClayPromotion = R70.round70ClayPromotion

round70PaperScaleDependentFundingConstructedIsTrue :
  round70PaperScaleDependentFundingConstructed ≡ true
round70PaperScaleDependentFundingConstructedIsTrue = refl

round70PaperBudgetOutrunningCriterionConstructedIsTrue :
  round70PaperBudgetOutrunningCriterionConstructed ≡ true
round70PaperBudgetOutrunningCriterionConstructedIsTrue = refl

round70PaperUniformPropagationChargeNecessaryIsFalse :
  round70PaperUniformPropagationChargeNecessary ≡ false
round70PaperUniformPropagationChargeNecessaryIsFalse = refl

round70PaperSummableFloorNoGoConstructedIsTrue :
  round70PaperSummableFloorNoGoConstructed ≡ true
round70PaperSummableFloorNoGoConstructedIsTrue = refl

round70PaperDyadicPropagationFundingFalsifiedIsTrue :
  round70PaperDyadicPropagationFundingFalsified ≡ true
round70PaperDyadicPropagationFundingFalsifiedIsTrue = refl

round70PaperBlockSupportSeparationNoGoConstructedIsTrue :
  round70PaperBlockSupportSeparationNoGoConstructed ≡ true
round70PaperBlockSupportSeparationNoGoConstructedIsTrue = refl

round70PaperCriticalAmplificationForcesStructuredConcentrationIsFalse :
  round70PaperCriticalAmplificationForcesStructuredConcentration ≡ false
round70PaperCriticalAmplificationForcesStructuredConcentrationIsFalse = refl

round70PaperPhysicalPropagationOutrunsBudgetIsFalse :
  round70PaperPhysicalPropagationOutrunsBudget ≡ false
round70PaperPhysicalPropagationOutrunsBudgetIsFalse = refl

round70PaperCriticalRatioBarrierIsFalse :
  round70PaperCriticalRatioBarrier ≡ false
round70PaperCriticalRatioBarrierIsFalse = refl

round70PaperClayPromotionIsFalse : round70PaperClayPromotion ≡ false
round70PaperClayPromotionIsFalse = refl
