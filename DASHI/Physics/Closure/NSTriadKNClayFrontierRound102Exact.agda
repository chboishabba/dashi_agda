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
-- Round101 left several candidate mechanisms. Round102 performs the algebra
-- needed to identify which of them are genuinely independent.
--
-- 1. The cross-radius recombination defect is factorized for an arbitrary
--    finite radial partition:
--
--      sum_{i<j} (lambda_i-lambda_j)(E_i q_j-E_j q_i).
--
--    A common transfer-density component q_i -> q_i+a E_i is invisible, so
--    only relative radial fluctuations matter.
--
-- 2. Ordinary energy-transfer conservation does not telescope that exterior
--    defect away. On a conservative family q=0 it becomes -E L, and an exact
--    rational witness has nonzero value.
--
-- 3. The standard unsigned critical product estimate leaves
--
--      (C X - nu) D,
--
--    and is therefore smallness-gated rather than an arbitrary-data barrier.
--
-- 4. Helical decomposition gives the stronger structural reduction:
--    nonlinear helicity conservation equates plus/minus critical-energy
--    tangents, hence unsigned critical production is twice their exchange.
--    Homochiral production vanishes. The same identity is lifted onto the
--    repository RealField carrier used by literal periodic Fourier modules.
--
-- 5. Opening the literal Round93 Waleffe factor sharpens the six mixed-helicity
--    sign classes further. In every heterochiral triad, the unsigned critical
--    production is exactly twice the critical-weighted transfer of the UNIQUE
--    minority-helicity leg. For minority k, for example,
--
--      Xdot = +/- 2 r_k (r_q-r_p) A.
--
--    The two homochiral sign patterns vanish. Thus eight helical sign patterns
--    reduce to three cyclic minority-leg geometries. Resonance supplies the
--    analytic target |r_q-r_p| <= r_k, so in the HH->low subclass with low
--    minority output the critical coefficient is charged at the low radius
--    squared. Minority-helicity and low-frequency are NOT identified globally;
--    comparable-scale and high-minority mixed triads remain inside the physical
--    exchange estimate.
--
-- 6. Once the critical Galerkin barrier is known, the standard compactness
--    exponents are no longer mysterious: interpolation gives L4_t H1, hence
--    L4_t L6; grad u is L2_t L3; the transport term is L4/3_t L2 and therefore
--    fits a Simon/Aubin--Lions negative-half derivative route. Round102 proves
--    those rational exponent identities exactly. The physical compactness
--    theorem is still not instantiated in the current Agda analysis library.
--
-- The submission cutset remains two theorem-sized obligations, but only the
-- first contains new 3-D dynamics:
--
--   A. UniformGalerkinCriticalBarrier, now a cutoff-uniform summation/absorption
--      theorem for the three minority-leg heterochiral geometries;
--   B. same-solution critical Galerkin -> Aubin--Lions/Simon -> limit weld.
--
-- Round90 already sends a same-solution CriticalBarrierFor to Serrin.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFiniteRadialTransferExteriorRound102Exact as Exterior
import DASHI.Physics.Closure.NSTriadKNThreeRadiusTransferExteriorRound102Exact as Three
import DASHI.Physics.Closure.NSTriadKNCriticalAbsoluteValueAbsorptionNoGoRound102Exact as AbsoluteNoGo
import DASHI.Physics.Closure.NSTriadKNHelicalCriticalExchangeReductionRound102Exact as Helical
import DASHI.Physics.Closure.NSTriadKNHelicalCriticalExchangeFieldRound102Exact as HelicalField
import DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegReductionRound102Exact as Minority
import DASHI.Physics.Closure.NSTriadKNCriticalAubinLionsExponentWeldRound102Exact as Exponents
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

round102RealFieldHelicalReductionClosed : Bool
round102RealFieldHelicalReductionClosed =
  HelicalField.round102RealFieldHelicalCriticalExchangeReductionClosed

round102AllMixedHelicityProductionReducedToMinorityLeg : Bool
round102AllMixedHelicityProductionReducedToMinorityLeg =
  Minority.round102AllMixedHelicityCriticalProductionReducesToMinorityLeg

round102CriticalAubinLionsExponentArithmeticClosed : Bool
round102CriticalAubinLionsExponentArithmeticClosed =
  Exponents.round102CriticalAubinLionsExponentArithmeticClosed

-- Remaining genuinely new 3-D estimate.
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

round102RealFieldHelicalReductionClosedIsTrue :
  round102RealFieldHelicalReductionClosed ≡ true
round102RealFieldHelicalReductionClosedIsTrue = refl

round102AllMixedHelicityProductionReducedToMinorityLegIsTrue :
  round102AllMixedHelicityProductionReducedToMinorityLeg ≡ true
round102AllMixedHelicityProductionReducedToMinorityLegIsTrue = refl

round102CriticalAubinLionsExponentArithmeticClosedIsTrue :
  round102CriticalAubinLionsExponentArithmeticClosed ≡ true
round102CriticalAubinLionsExponentArithmeticClosedIsTrue = refl

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
