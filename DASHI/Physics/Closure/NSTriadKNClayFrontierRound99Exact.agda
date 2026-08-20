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
-- The generic packet/boundary normalization is also welded directly to the
-- same compact-Gamma raw transfer, division-free over the abstract RealField.
--
-- The remaining object is NOT hidden behind an opaque Set-valued receipt.  It
-- is exposed below as the already-existing literal nonlinear component of
--
--       qdot D - q Ddot
--
-- on the physical finite Galerkin carrier.  The outstanding theorem is a
-- cutoff-uniform integrated expenditure estimate for THIS function.
--
-- Round99 also strengthens the Round91 homogeneity audit: for every proposed
-- nonnegative constant C, amplitude a=C+1 gives a^3 > C a^2.  Therefore a
-- static amplitude-free HH<=C*D closure is mathematically impossible; the last
-- estimate must exploit same-trajectory transfer dynamics rather than import a
-- conditional critical-amplitude smallness hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift
import DASHI.Physics.Closure.NSTriadKNLiteralRHSRelativeGrowthSplitRound83Exact as Split
import DASHI.Physics.Closure.NSTriadKNProjectedCompactGammaPressureEliminationRound99Exact as Pressure
import DASHI.Physics.Closure.NSTriadKNPositiveTransferOffPacketCoercivityRound99Exact as OffPacket
import DASHI.Physics.Closure.NSTriadKNPhysicalGammaBoundaryTransferSameObjectRound99Exact as Boundary
import DASHI.Physics.Closure.NSTriadKNGradientTensorFourierSymbolRound89Exact as GradientTensor
import DASHI.Physics.Closure.NSTriadKNViscousWeightedHHLowTensorFactorizationRound89Exact as HHTensor
import DASHI.Physics.Closure.NSTriadKNHHCriticalAmplitudeAbsorptionRound91Exact as CriticalAmplitude
import DASHI.Physics.Closure.NSTriadKNCubicQuadraticUniformAbsorptionNoGoRound99Exact as NoGo
import DASHI.Physics.Closure.NSTriadKNPhysicalPeriodicBonyEnumerationRound92Exact as Bony
import DASHI.Physics.Closure.NSTriadKNIntegratedDangerOccupationWeldRound92Exact as Occupation

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

round99UniformAmplitudeFreeCubicAbsorptionPossible : Bool
round99UniformAmplitudeFreeCubicAbsorptionPossible =
  NoGo.round99StaticHHBoundCanSupplyUniformAmplitudeFreeAbsorption

round99LiteralPhysicalBonyClassificationClosed : Bool
round99LiteralPhysicalBonyClassificationClosed =
  Bony.round92LiteralPhysicalBonyClassificationExhaustive

round99IntegratedDangerOccupationCompilerClosed : Bool
round99IntegratedDangerOccupationCompilerClosed =
  Occupation.round92IntegratedSignedCriticalEstimateFromOccupationConstructed

------------------------------------------------------------------------
-- Literal owner of the sole surviving nonlinear core.
------------------------------------------------------------------------

remainingProjectedBoundaryFluxVariationCore :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model →
  C3.Carrier (LP.realField model)
remainingProjectedBoundaryFluxVariationCore = Split.nonlinearRelativeGrowthCore

remainingCoreIsLiteralNonlinearRelativeGrowth :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  remainingProjectedBoundaryFluxVariationCore datum
  ≡ Split.nonlinearRelativeGrowthCore datum
remainingCoreIsLiteralNonlinearRelativeGrowth datum = refl

-- Exact current frontier flags.  `true` here means one producer survives; it
-- does not assert the missing inequality or Clay promotion.
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

round99UniformAmplitudeFreeCubicAbsorptionPossibleIsFalse :
  round99UniformAmplitudeFreeCubicAbsorptionPossible ≡ false
round99UniformAmplitudeFreeCubicAbsorptionPossibleIsFalse = refl

round99ProjectedBoundaryFluxVariationProducerSurvivesIsTrue :
  round99ProjectedBoundaryFluxVariationProducerSurvives ≡ true
round99ProjectedBoundaryFluxVariationProducerSurvivesIsTrue = refl

round99ClayPromotionIsFalse : round99ClayPromotion ≡ false
round99ClayPromotionIsFalse = refl
