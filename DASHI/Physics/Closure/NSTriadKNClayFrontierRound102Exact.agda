module DASHI.Physics.Closure.NSTriadKNClayFrontierRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
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
-- The top-down endpoint remains exactly two theorem-sized obligations:
--
--   A. a cutoff-uniform arbitrary-data Galerkin H^(1/2)/H^(3/2) barrier;
--   B. the same-solution Galerkin -> Aubin--Lions/Simon -> limit weld.
--
-- Round102 materially compresses the NEW dynamics inside A.
--
-- * The finite radial recombination defect is the pairwise exterior sum
--     sum_{i<j}(lambda_i-lambda_j)(E_i q_j-E_j q_i).
--   Ordinary energy conservation does not kill it.
--
-- * Generic unsigned critical absolute-value absorption is smallness-gated.
--
-- * Helicity splits the critical energy into plus/minus curl sectors.
--   Homochiral nonlinear critical production vanishes; all production is
--   heterochiral exchange.
--
-- * Opening the literal Round93 Waleffe factor reduces the six mixed-helicity
--   sign classes to THREE cyclic geometries: critical production is twice the
--   critical-weighted transfer of the unique minority-helicity leg.  This is
--   proved both over rationals and the repository RealField carrier.
--
-- * The Waleffe area polynomial is exactly the Heron product.  In HH->low
--   geometry the minority-leg factor and triangle geometry give, before
--   division, O(k^2) when the low leg is the helicity minority and O(k q)
--   when a high leg is the minority.  Thus the high-minority case still gains
--   one full low/high ratio over the naive O(q^2) high-high cost.
--
-- * High-frequency support itself is NOT convolution-closed; an exact lattice
--   witness rules out replacing this coefficient-level null structure by a
--   support-counting/quasi-trapping shortcut.
--
-- * Once A is supplied, the critical Aubin--Lions exponent arithmetic is
--   already exact: L^infinity H^(1/2) cap L^2 H^(3/2) gives L^4 H^1, and the
--   nonlinear time derivative fits the standard L^(4/3) H^(-1/2) route.
--
-- Therefore the live frontier inside A is no longer "find some mysterious
-- Schur exponent".  It is the source-native SUMMATION/ABSORPTION theorem that
-- transports these literal helical triangle gains through all physical
-- Galerkin triads, together with the comparable-scale/local sector, into one
-- cutoff-uniform critical barrier.  Existing near-centered/finite-overlap
-- machinery is reusable, but its physical moment/amplitude envelope is not
-- silently assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFiniteRadialTransferExteriorRound102Exact as Exterior
import DASHI.Physics.Closure.NSTriadKNThreeRadiusTransferExteriorRound102Exact as Three
import DASHI.Physics.Closure.NSTriadKNCriticalAbsoluteValueAbsorptionNoGoRound102Exact as AbsoluteNoGo
import DASHI.Physics.Closure.NSTriadKNHelicalCriticalExchangeReductionRound102Exact as Helical
import DASHI.Physics.Closure.NSTriadKNHelicalCriticalExchangeFieldRound102Exact as HelicalField
import DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegReductionRound102Exact as Minority
import DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegFieldRound102Exact as MinorityField
import DASHI.Physics.Closure.NSTriadKNWaleffeHeronPolynomialRound102Exact as Heron
import DASHI.Physics.Closure.NSTriadKNWaleffeHHMinorityNumeratorGainRound102Exact as HHGain
import DASHI.Physics.Closure.NSTriadKNHighFrequencySupportConvolutionNoGoRound102Exact as SupportNoGo
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

round102RealFieldMinorityLegNormalFormClosed : Bool
round102RealFieldMinorityLegNormalFormClosed =
  MinorityField.round102RealFieldMinorityLegNormalFormClosed

round102WaleffeHeronPolynomialClosed : Bool
round102WaleffeHeronPolynomialClosed =
  Heron.round102WaleffeHeronPolynomialFactorizationClosed

round102LowMinorityHHNumeratorGainClosed : Bool
round102LowMinorityHHNumeratorGainClosed =
  HHGain.round102LowMinorityHHWaleffeNumeratorGainClosed

round102HighMinorityHHNumeratorGainClosed : Bool
round102HighMinorityHHNumeratorGainClosed =
  HHGain.round102HighMinorityHHWaleffeNumeratorGainClosed

round102HighFrequencySupportConvolutionClosed : Bool
round102HighFrequencySupportConvolutionClosed =
  SupportNoGo.round102HighFrequencySupportConvolutionClosed

round102CriticalAubinLionsExponentArithmeticClosed : Bool
round102CriticalAubinLionsExponentArithmeticClosed =
  Exponents.round102CriticalAubinLionsExponentArithmeticClosed

-- Remaining genuinely new 3-D theorem: literal physical helical/Waleffe
-- identification + summation/absorption across all Galerkin triads, including
-- the comparable-scale/local sector, into the uniform critical barrier.
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

round102RealFieldMinorityLegNormalFormClosedIsTrue :
  round102RealFieldMinorityLegNormalFormClosed ≡ true
round102RealFieldMinorityLegNormalFormClosedIsTrue = refl

round102WaleffeHeronPolynomialClosedIsTrue :
  round102WaleffeHeronPolynomialClosed ≡ true
round102WaleffeHeronPolynomialClosedIsTrue = refl

round102LowMinorityHHNumeratorGainClosedIsTrue :
  round102LowMinorityHHNumeratorGainClosed ≡ true
round102LowMinorityHHNumeratorGainClosedIsTrue = refl

round102HighMinorityHHNumeratorGainClosedIsTrue :
  round102HighMinorityHHNumeratorGainClosed ≡ true
round102HighMinorityHHNumeratorGainClosedIsTrue = refl

round102HighFrequencySupportConvolutionClosedIsFalse :
  round102HighFrequencySupportConvolutionClosed ≡ false
round102HighFrequencySupportConvolutionClosedIsFalse = refl

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
