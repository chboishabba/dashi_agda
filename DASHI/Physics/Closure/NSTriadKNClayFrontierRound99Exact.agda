module DASHI.Physics.Closure.NSTriadKNClayFrontierRound99Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND99 / ONE-PRODUCER MATHEMATICAL FRONTIER
--
-- This file is deliberately a frontier *reduction*, not a receipt claiming an
-- estimate that has not been proved.
--
-- Round99 removes two previously counted analytic producers from the shortest
-- compact-Gamma route:
--
--   (1) pressure is not an independent tangent: the literal finite Galerkin
--       vector field already contains the Leray-projected nonlinearity;
--
--   (2) on the positive-transfer branch where transfer-Gamma is active, the
--       off-packet boundary term -F E has favourable sign, and the remaining
--       cross-dissipation is spectrally coercive.
--
-- The generic packet/boundary normalization has also been welded directly to
-- the same compact-Gamma raw transfer, division-free over the abstract
-- RealField carrier.
--
-- What remains is ONE genuinely new PDE estimate: cutoff-uniform expenditure
-- control for the nonlinear first variation of the SAME projected boundary
-- transfer.  It must control the nonlinear piece of
--
--       qdot D - q Ddot
--
-- on the literal Galerkin carrier strongly enough to feed the existing
-- integrated compact-Gamma escape/critical-barrier machinery.
--
-- Why this cannot honestly be replaced by an existing conditional theorem:
-- the closed HH/Bony estimates yield a cubic-production bound of the form
--
--       N_hi <= C A_* D,
--
-- while the Cheskidov--Shvydkoy absorption theorem requires A_* below a
-- viscosity threshold.  Their cited result is a conditional regularity
-- criterion; it does not supply that smallness for arbitrary Leray solutions.
-- Thus setting a critical-amplitude hypothesis to true would merely assume the
-- missing global-regularity mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNProjectedCompactGammaPressureEliminationRound99Exact as Pressure
import DASHI.Physics.Closure.NSTriadKNPositiveTransferOffPacketCoercivityRound99Exact as OffPacket
import DASHI.Physics.Closure.NSTriadKNPhysicalGammaBoundaryTransferSameObjectRound99Exact as Boundary
import DASHI.Physics.Closure.NSTriadKNGradientTensorFourierSymbolRound89Exact as GradientTensor
import DASHI.Physics.Closure.NSTriadKNViscousWeightedHHLowTensorFactorizationRound89Exact as HHTensor
import DASHI.Physics.Closure.NSTriadKNHHCriticalAmplitudeAbsorptionRound91Exact as CriticalAmplitude
import DASHI.Physics.Closure.NSTriadKNPhysicalPeriodicBonyEnumerationRound92Exact as Bony
import DASHI.Physics.Closure.NSTriadKNIntegratedDangerOccupationWeldRound92Exact as Occupation

-- Exact reductions now available on the branch.
round99ProjectedPressureAlreadyInsideLerayVectorField : Bool
round99ProjectedPressureAlreadyInsideLerayVectorField =
  Pressure.round99CompactGammaUsesProjectedGalerkinTangent

round99SeparatePressureEstimateRequired : Bool
round99SeparatePressureEstimateRequired =
  Pressure.round99PressureThreeWayEstimateIsShortestPathProducer

round99PositiveTransferOffPacketNonlinearTaxRequired : Bool
round99PositiveTransferOffPacketNonlinearTaxRequired =
  OffPacket.round99AdditionalOffPacketNonlinearOccupationLemmaRequired

round99GenericBoundaryTransferSameObjectClosed : Bool
round99GenericBoundaryTransferSameObjectClosed =
  Boundary.round99PhysicalGammaBoundaryTransferSameObjectWeldClosed

round99DerivativeWeightedFourierTensorIdentityClosed : Bool
round99DerivativeWeightedFourierTensorIdentityClosed =
  GradientTensor.round89GradientTensorFourierSymbolIdentityClosed

round99WeightedHHTensorDivergenceIdentityClosed : Bool
round99WeightedHHTensorDivergenceIdentityClosed =
  HHTensor.round89WeightedHHTensorDivergenceIdentityClosed

round99RawHHBoundAloneSufficesForViscousAbsorption : Bool
round99RawHHBoundAloneSufficesForViscousAbsorption =
  CriticalAmplitude.round91RawHHHMinusOneSquareBoundAloneImpliesViscousAbsorption

round99LiteralPhysicalBonyClassificationClosed : Bool
round99LiteralPhysicalBonyClassificationClosed =
  Bony.round92LiteralPhysicalBonyClassificationExhaustive

round99IntegratedDangerOccupationCompilerClosed : Bool
round99IntegratedDangerOccupationCompilerClosed =
  Occupation.round92IntegratedSignedCriticalEstimateFromOccupationConstructed

------------------------------------------------------------------------
-- The sole remaining theorem-sized PDE producer.
--
-- This is intentionally represented as an uninhabited interface TYPE, not a
-- postulate and not an assumed field in a theorem-producing record.  A future
-- module closes Round99 only by constructing a term from the literal physical
-- Galerkin/compact-Gamma data.
------------------------------------------------------------------------

record PhysicalProjectedBoundaryFluxVariationExpenditure : Set₁ where
  field
    -- The exact carrier/inequality is intentionally not weakened to a generic
    -- scalar receipt here.  The physical implementation must itself expose:
    --
    --   * the literal cutoff Galerkin solution family;
    --   * the canonical shell selector / packet boundary;
    --   * q, qdot_N, D, Ddot_N from the same projected vector field;
    --   * the existing weighted coercive envelope;
    --   * a cutoff-independent finite remainder;
    --   * the inequality which pays the nonlinear relative-growth core by
    --     absorbed envelope plus that remainder.
    --
    -- These named components are theorem-construction requirements, not
    -- independent assumptions that downstream code may silently fill.
    LiteralPhysicalConstruction : Set
    literalPhysicalConstruction : LiteralPhysicalConstruction

    SameObjectNonlinearRelativeGrowth : Set
    sameObjectNonlinearRelativeGrowth : SameObjectNonlinearRelativeGrowth

    CutoffUniformCoerciveExpenditure : Set
    cutoffUniformCoerciveExpenditure : CutoffUniformCoerciveExpenditure

    FiniteEndpointRemainder : Set
    finiteEndpointRemainder : FiniteEndpointRemainder

    nonlinearVariationPaidByExpenditure : Set
    nonlinearVariationPaidByExpenditureProof :
      nonlinearVariationPaidByExpenditure

open PhysicalProjectedBoundaryFluxVariationExpenditure public

-- This is the exact current count, not a promotion claim.
round99GenuineAnalyticProducerCount : Bool
round99GenuineAnalyticProducerCount = true

round99PressureProducerSurvives : Bool
round99PressureProducerSurvives = false

round99OffPacketProducerSurvives : Bool
round99OffPacketProducerSurvives = false

round99ProjectedBoundaryFluxVariationProducerSurvives : Bool
round99ProjectedBoundaryFluxVariationProducerSurvives = true

round99ClayPromotion : Bool
round99ClayPromotion = false

round99SeparatePressureEstimateRequiredIsFalse :
  round99SeparatePressureEstimateRequired ≡ false
round99SeparatePressureEstimateRequiredIsFalse = refl

round99PositiveTransferOffPacketNonlinearTaxRequiredIsFalse :
  round99PositiveTransferOffPacketNonlinearTaxRequired ≡ false
round99PositiveTransferOffPacketNonlinearTaxRequiredIsFalse = refl

round99RawHHBoundAloneSufficesForViscousAbsorptionIsFalse :
  round99RawHHBoundAloneSufficesForViscousAbsorption ≡ false
round99RawHHBoundAloneSufficesForViscousAbsorptionIsFalse = refl

round99ProjectedBoundaryFluxVariationProducerSurvivesIsTrue :
  round99ProjectedBoundaryFluxVariationProducerSurvives ≡ true
round99ProjectedBoundaryFluxVariationProducerSurvivesIsTrue = refl

round99ClayPromotionIsFalse : round99ClayPromotion ≡ false
round99ClayPromotionIsFalse = refl
