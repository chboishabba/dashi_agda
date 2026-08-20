module DASHI.Physics.Closure.NSTriadKNClayFrontierRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the Navier-Stokes
-- Equations".
-- DOI: 10.1007/BF02392477.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: Zhen Lei; Fang-Hua Lin; Yi Zhou.
-- Title: "Structure of Helicity and Global Solutions of Incompressible
-- Navier-Stokes Equation".
-- DOI: 10.1007/s00205-015-0884-8.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator estimates and the Euler and Navier-Stokes equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Jacques Simon.
-- Title: "Compact Sets in the Space L^p(0,T;B)".
-- DOI: 10.1007/BF01762360.
--
-- ROUND102 / TWO-OBLIGATION CLAY FRONTIER
--
-- Round101 left several candidate mechanisms.  Round102 performs the algebra
-- needed to identify which of them are genuinely independent.
--
-- 1. The cross-radius recombination defect is now factorized for an arbitrary
--    finite radial partition as
--
--      sum_{i<j} (lambda_i-lambda_j)(E_i q_j-E_j q_i).
--
--    A common transfer-density component q_i -> q_i+a E_i is invisible, so
--    only relative radial fluctuations matter.
--
-- 2. Ordinary energy-transfer conservation does not telescope that exterior
--    defect away.  On a conservative family q=0 it becomes -E L, and an exact
--    rational witness has nonzero value.  Thus conservation alone cannot be
--    promoted to the missing critical barrier.
--
-- 3. The standard unsigned critical product estimate has residual
--
--      (C X - nu) D,
--
--    so it is smallness-gated.  Arbitrary-data closure requires additional
--    signed structure.
--
-- 4. Helical decomposition supplies exactly such a structural reduction:
--    nonlinear helicity conservation equates the plus/minus critical-energy
--    tangents, hence unsigned critical production is twice their exchange.
--    Homochiral production is therefore zero.  The only new nonlinear
--    mechanism still required is a cutoff-uniform estimate on HETEROCHIRAL
--    critical exchange strong enough to produce the Galerkin H^(1/2)/H^(3/2)
--    barrier.
--
-- The mathematical submission cutset is therefore still two theorem-sized
-- obligations, but only the first contains frontier 3-D dynamics:
--
--   A. UniformGalerkinCriticalBarrier, now sharpened to a heterochiral-exchange
--      estimate plus viscosity / integrable lower-order budget;
--   B. same-solution critical Galerkin -> Aubin--Lions/Simon -> limit weld.
--
-- Round90 already consumes the resulting same-solution CriticalBarrierFor and
-- sends it to the Serrin continuation endpoint.  No Clay promotion is made.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFiniteRadialTransferExteriorRound102Exact as Exterior
import DASHI.Physics.Closure.NSTriadKNThreeRadiusTransferExteriorRound102Exact as Three
import DASHI.Physics.Closure.NSTriadKNCriticalAbsoluteValueAbsorptionNoGoRound102Exact as AbsoluteNoGo
import DASHI.Physics.Closure.NSTriadKNHelicalCriticalExchangeReductionRound102Exact as Helical
import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical

round102FiniteRadialExteriorFactorizationClosed : Bool
round102FiniteRadialExteriorFactorizationClosed =
  Exterior.round102FiniteRadialDefectExteriorFactorizationClosed

round102EnergyConservationAloneKillsRadialDefect : Bool
round102EnergyConservationAloneKillsRadialDefect =
  Three.round102EnergyConservationAloneKillsRadialDefect

round102UnsignedCriticalAbsoluteEstimateClosesArbitraryDataBarrier : Bool
round102UnsignedCriticalAbsoluteEstimateClosesArbitraryDataBarrier =
  AbsoluteNoGo.round102UnsignedCriticalProductEstimateIsArbitraryDataBarrier

round102HomochiralCriticalProductionEliminated : Bool
round102HomochiralCriticalProductionEliminated =
  Helical.round102HomochiralCriticalProductionEliminatedByHelicity

round102CriticalProductionReducedToHeterochiralExchange : Bool
round102CriticalProductionReducedToHeterochiralExchange =
  Helical.round102CriticalProductionReducesToHeterochiralExchange

-- This is the remaining genuinely new 3-D estimate.  It is deliberately false
-- until the literal periodic Galerkin nonlinearity is proved to satisfy the
-- required cutoff-uniform heterochiral expenditure bound.
round102PhysicalHeterochiralCriticalExchangeBarrierClosed : Bool
round102PhysicalHeterochiralCriticalExchangeBarrierClosed = false

round102UniformGalerkinCriticalBarrierClosed : Bool
round102UniformGalerkinCriticalBarrierClosed = false

round102SameSolutionCriticalLimitWeldClosed : Bool
round102SameSolutionCriticalLimitWeldClosed =
  Critical.criticalAubinLionsInstantiated

round102FiniteRadialExteriorFactorizationClosedIsTrue :
  round102FiniteRadialExteriorFactorizationClosed ≡ true
round102FiniteRadialExteriorFactorizationClosedIsTrue = refl

round102EnergyConservationAloneKillsRadialDefectIsFalse :
  round102EnergyConservationAloneKillsRadialDefect ≡ false
round102EnergyConservationAloneKillsRadialDefectIsFalse = refl

round102UnsignedCriticalAbsoluteEstimateClosesArbitraryDataBarrierIsFalse :
  round102UnsignedCriticalAbsoluteEstimateClosesArbitraryDataBarrier ≡ false
round102UnsignedCriticalAbsoluteEstimateClosesArbitraryDataBarrierIsFalse = refl

round102HomochiralCriticalProductionEliminatedIsTrue :
  round102HomochiralCriticalProductionEliminated ≡ true
round102HomochiralCriticalProductionEliminatedIsTrue = refl

round102CriticalProductionReducedToHeterochiralExchangeIsTrue :
  round102CriticalProductionReducedToHeterochiralExchange ≡ true
round102CriticalProductionReducedToHeterochiralExchangeIsTrue = refl

round102PhysicalHeterochiralCriticalExchangeBarrierClosedIsFalse :
  round102PhysicalHeterochiralCriticalExchangeBarrierClosed ≡ false
round102PhysicalHeterochiralCriticalExchangeBarrierClosedIsFalse = refl

round102UniformGalerkinCriticalBarrierClosedIsFalse :
  round102UniformGalerkinCriticalBarrierClosed ≡ false
round102UniformGalerkinCriticalBarrierClosedIsFalse = refl

round102SameSolutionCriticalLimitWeldClosedIsFalse :
  round102SameSolutionCriticalLimitWeldClosed ≡ false
round102SameSolutionCriticalLimitWeldClosedIsFalse = refl

round102ClayPromotion : Bool
round102ClayPromotion = false

round102ClayPromotionIsFalse : round102ClayPromotion ≡ false
round102ClayPromotionIsFalse = refl
