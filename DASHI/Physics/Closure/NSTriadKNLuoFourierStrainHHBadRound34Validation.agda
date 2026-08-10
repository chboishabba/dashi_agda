module DASHI.Physics.Closure.NSTriadKNLuoFourierStrainHHBadRound34Validation where

------------------------------------------------------------------------
-- Round Thirty-Four cumulative Navier--Stokes validation root.
--
-- This root deliberately imports the previous stack before the new physical
-- producers, so repairs to the Round-30 finite-system API are checked against
-- all downstream Round-31--33 consumers.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoSameObjectSharpGainRound33Validation

import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as Transverse
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as PhysicalField

import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Cutoff
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainMultiplierRound34Exact as Strain
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainL2Round34Exact as StrainL2
import DASHI.Physics.Closure.NSTriadKNHHBadSummableDyadicGainRound34Exact as HHBad
import DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact as Com
import DASHI.Physics.Closure.NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact as Bishop

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

finiteAuditRegression :
  Audit.literalProjectedGalerkinSumConstructed ≡ true
finiteAuditRegression =
  Audit.literalProjectedGalerkinSumConstructedIsTrue

projectedTransversalityRegression :
  Transverse.projectedNonlinearityTransverseClosed ≡ true
projectedTransversalityRegression =
  Transverse.projectedNonlinearityTransverseClosedIsTrue

literalCoefficientRegression :
  Coefficient.literalViscousQuadraticCoefficientClosed ≡ true
literalCoefficientRegression =
  Coefficient.literalViscousQuadraticCoefficientClosedIsTrue

physicalFieldRegression :
  PhysicalField.concretePhysicalGalerkinVectorFieldClosed ≡ true
physicalFieldRegression =
  PhysicalField.concretePhysicalGalerkinVectorFieldClosedIsTrue

canonicalCutoffSystemRegression :
  Cutoff.canonicalCutoffSameObjectFiniteSystemClosed ≡ true
canonicalCutoffSystemRegression =
  Cutoff.canonicalCutoffSameObjectFiniteSystemClosedIsTrue

rawStateFamilyStillOpenRegression :
  Cutoff.cutoffSameObjectFamilyConstructedForRawStateCarrier ≡ false
rawStateFamilyStillOpenRegression =
  Cutoff.cutoffSameObjectFamilyConstructedForRawStateCarrierIsFalse

fourierStrainRegression :
  Strain.periodicFourierStrainMultiplierExactClosed ≡ true
fourierStrainRegression =
  Strain.periodicFourierStrainMultiplierExactClosedIsTrue

principalValueKernelStillOpenRegression :
  Strain.physicalPeriodicPrincipalValueKernelConstructed ≡ false
principalValueKernelStillOpenRegression =
  Strain.physicalPeriodicPrincipalValueKernelConstructedIsFalse

fourierStrainL2Regression :
  StrainL2.periodicFourierStrainL2Closed ≡ true
fourierStrainL2Regression =
  StrainL2.periodicFourierStrainL2ClosedIsTrue

kernelIncrementStillOpenRegression :
  StrainL2.periodicStrainKernelIncrementBoundConstructed ≡ false
kernelIncrementStillOpenRegression =
  StrainL2.periodicStrainKernelIncrementBoundConstructedIsFalse

hhBadSummabilityRegression :
  HHBad.hhBadDyadicTargetProfileSummableClosed ≡ true
hhBadSummabilityRegression =
  HHBad.hhBadDyadicTargetProfileSummableClosedIsTrue

physicalHHBadProfileStillOpenRegression :
  HHBad.physicalHHBadGainProfileProduced ≡ false
physicalHHBadProfileStillOpenRegression =
  HHBad.physicalHHBadGainProfileProducedIsFalse

cotlarEnvelopeRegression :
  Com.rationalCotlarDyadicEnvelopeClosed ≡ true
cotlarEnvelopeRegression =
  Com.rationalCotlarDyadicEnvelopeClosedIsTrue

physicalComDecayStillOpenRegression :
  Com.physicalTwoSidedComPairDecayConstructed ≡ false
physicalComDecayStillOpenRegression =
  Com.physicalTwoSidedComPairDecayConstructedIsFalse

bishopCoordinateSemanticsRegression :
  Bishop.murrayBishopGalerkinPolynomialSemanticsClosed ≡ true
bishopCoordinateSemanticsRegression =
  Bishop.murrayBishopGalerkinPolynomialSemanticsClosedIsTrue

physicalBishopEquivalenceStillOpenRegression :
  Bishop.physicalBishopCoordinateEquivalenceConstructed ≡ false
physicalBishopEquivalenceStillOpenRegression =
  Bishop.physicalBishopCoordinateEquivalenceConstructedIsFalse
