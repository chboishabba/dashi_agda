{-# OPTIONS --safe #-}
module DASHI.Unified.YMBalabanRGPhysicalBoundaryTOEExact where

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F
--
-- O. Objective.
-- Normalize the current Bałaban RG, regular-E, Casimir, stress, and
-- continuum non-promotion owners onto one TOE-facing surface.
--
-- R. Reuse.
-- Round559 owns the canonical TOE Yang-Mills convergence exports.
-- Round249 owns the current function-valued regular-E localization bridge.
-- Round250 owns the active raw CMP119 -> BC1 continuation.
-- The trace/inverse-coupling firewall owns the slope/value distinction.
-- The Lorentzian timelike-energy firewall owns trace != active stress.
--
-- C. Concrete result.
-- This module exposes only existing theorem levels and exact fail-closed facts.
-- It creates no second RG, stress, Casimir, continuum, or antigravity model.
--
-- S. Preconditions and invariants.
-- A compiler proof does not become a physical source proof.
-- A finite RG theorem does not become a four-dimensional continuum theorem.
-- A negative trace does not become negative active stress.
-- The RG slope is not the inverse-coupling value.
-- ESD surfaces are not edited.
--
-- L. Lane.
-- This is the normalized Yang-Mills physical-boundary TOE lane.
--
-- P. Postconditions.
-- TOE consumers can reach current scale-density, regular-E, Casimir, stress,
-- S4/P3G, and non-promotion owners from one import.
--
-- G. Governance.
-- Original source attribution remains in theorem-owner modules.
-- No coincidence or representation adapter is promoted to a same-object proof.
--
-- F. Verification.
-- Read-back must show each export below resolves to its canonical owner.
-- Kernel certification still requires an Agda or exact-head CI receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as YMTOE
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationToActiveRawRound249Exact as R249
import DASHI.Physics.YangMills.BalabanCMP119ActiveRawToBC1Round250Exact as R250
import DASHI.Physics.Foundations.CMP119AntigravityTraceCoefficientInverseCouplingFirewallExact as TraceSlope
import DASHI.Physics.Foundations.CMP119AntigravityTraceVsActiveStressFirewallExact as TraceStress

------------------------------------------------------------------------
-- Source-native RG scale density.
------------------------------------------------------------------------

toeBoundaryCMP119SourceNativeStateLevel : ProofLevel
toeBoundaryCMP119SourceNativeStateLevel =
  CMP119.cmp119SourceNativeStateLevel

toeBoundaryCMP119ScalarProjectionLevel : ProofLevel
toeBoundaryCMP119ScalarProjectionLevel =
  CMP119.cmp119SourceNativeScalarProjectionLevel

toeBoundaryCMP119LiteralCompleteDensityLevel : ProofLevel
toeBoundaryCMP119LiteralCompleteDensityLevel =
  CMP119.cmp119LiteralCompleteDensityInstantiationLevel

toeBoundaryCMP119LiteralSectorNormBoundsLevel : ProofLevel
toeBoundaryCMP119LiteralSectorNormBoundsLevel =
  CMP119.cmp119LiteralSectorNormProjectionBoundsLevel

------------------------------------------------------------------------
-- Current regular-E localization and active BC1 continuation.
------------------------------------------------------------------------

toeBoundaryRegularEFunctionalToRawCompilerLevel : ProofLevel
toeBoundaryRegularEFunctionalToRawCompilerLevel =
  R249.functionalLocalizationToRawDecoderCompilerLevel

toeBoundaryRegularELiteralLocalizationLevel : ProofLevel
toeBoundaryRegularELiteralLocalizationLevel =
  R249.literalFunctionalRegularELocalizationCarrierLevel

toeBoundaryRegularESameRawFunctionLevel : ProofLevel
toeBoundaryRegularESameRawFunctionLevel =
  R249.literalFunctionalToActiveRawRegularEWeldLevel

toeBoundaryActiveRawToBC1CompilerLevel : ProofLevel
toeBoundaryActiveRawToBC1CompilerLevel =
  R250.activeRawToBC1CompilerLevel

toeBoundaryActiveRawSameRegularELevel : ProofLevel
toeBoundaryActiveRawSameRegularELevel =
  R250.activeRawBC1SameRegularELevel

toeBoundaryPreferredConcreteRawToBC1CompilerLevel : ProofLevel
toeBoundaryPreferredConcreteRawToBC1CompilerLevel =
  R250.preferredConcreteActiveRawToBC1CompilerLevel

toeBoundaryCMP122ConcreteSourceWitnessLevel : ProofLevel
toeBoundaryCMP122ConcreteSourceWitnessLevel =
  R250.preferredConcreteCMP122SourceWitnessLevel

toeBoundarySecondVariationLinearityLevel : ProofLevel
toeBoundarySecondVariationLinearityLevel =
  R250.physicalSecondVariationLinearityLevel

toeBoundaryEquation51ActiveRegularELevel : ProofLevel
toeBoundaryEquation51ActiveRegularELevel =
  R250.literalCMP109Equation51OnActiveRegularELevel

toeBoundaryCMP116DemandExtractionLevel : ProofLevel
toeBoundaryCMP116DemandExtractionLevel =
  R250.literalCMP116FiniteNormalizedDemandExtractionLevel

------------------------------------------------------------------------
-- Casimir and stress reuse.
------------------------------------------------------------------------

toeBoundaryAdjointCasimirStrictPositivityLevel : ProofLevel
toeBoundaryAdjointCasimirStrictPositivityLevel =
  YMTOE.toeAdjointCasimirStrictPositivityLevel

toeBoundaryWilsonGhostHaarCasimirLevel : ProofLevel
toeBoundaryWilsonGhostHaarCasimirLevel =
  YMTOE.toeWilsonGhostHaarToClassifiedCasimirLevel

toeBoundaryMetricStressCompilerLevel : ProofLevel
toeBoundaryMetricStressCompilerLevel =
  YMTOE.toeMetricStressRepresentationCompilerLevel

toeBoundaryLiteralMetricStressLevel : ProofLevel
toeBoundaryLiteralMetricStressLevel =
  YMTOE.toeLiteralMetricStressRepresentationLevel

toeBoundaryStressSameFamilyLevel : ProofLevel
toeBoundaryStressSameFamilyLevel =
  YMTOE.toeStressLevel2SameFamilyRecoveryLevel

toeBoundaryStressShortDistanceOPELevel : ProofLevel
toeBoundaryStressShortDistanceOPELevel =
  YMTOE.toeStressLevel2ShortDistanceOPELevel

------------------------------------------------------------------------
-- Exact semantic firewalls.
------------------------------------------------------------------------

toeBoundaryRGSlopeMayReplaceInverseCouplingValue : Bool
toeBoundaryRGSlopeMayReplaceInverseCouplingValue =
  TraceSlope.rgSlopeCanBeSubstitutedForInverseCouplingValue

toeBoundaryRGSlopeMayReplaceInverseCouplingValueIsFalse :
  toeBoundaryRGSlopeMayReplaceInverseCouplingValue ≡ false
toeBoundaryRGSlopeMayReplaceInverseCouplingValueIsFalse =
  TraceSlope.rgSlopeCanBeSubstitutedForInverseCouplingValueIsFalse

toeBoundaryNegativeTraceAloneClosesNegativeActiveStress : Bool
toeBoundaryNegativeTraceAloneClosesNegativeActiveStress =
  TraceStress.negativeTraceAloneClosesNegativeActiveStress

toeBoundaryNegativeTraceAloneClosesNegativeActiveStressIsFalse :
  toeBoundaryNegativeTraceAloneClosesNegativeActiveStress ≡ false
toeBoundaryNegativeTraceAloneClosesNegativeActiveStressIsFalse =
  TraceStress.negativeTraceAloneClosesNegativeActiveStressIsFalse

toeBoundaryTimelikeEnergyDensityControlRequired : Bool
toeBoundaryTimelikeEnergyDensityControlRequired =
  TraceStress.timelikeEnergyDensityControlStillRequired

toeBoundaryTimelikeEnergyDensityControlRequiredIsTrue :
  toeBoundaryTimelikeEnergyDensityControlRequired ≡ true
toeBoundaryTimelikeEnergyDensityControlRequiredIsTrue =
  TraceStress.timelikeEnergyDensityControlStillRequiredIsTrue

------------------------------------------------------------------------
-- S4/P3G and continuum/Clay non-promotion.
------------------------------------------------------------------------

toeBoundaryAntigravityS4CompilerLevel : ProofLevel
toeBoundaryAntigravityS4CompilerLevel =
  YMTOE.toeAntigravityS4PhysicalMinCutCompilerLevel

toeBoundaryAntigravityP3GCompilerLevel : ProofLevel
toeBoundaryAntigravityP3GCompilerLevel =
  YMTOE.toeAntigravityP3GPhysicalProducerCompilerLevel

toeBoundaryFlat4DContinuumPromoted : Bool
toeBoundaryFlat4DContinuumPromoted =
  YMTOE.toeFlat4DContinuumTransferProvedHere

toeBoundaryFlat4DContinuumPromotedIsFalse :
  toeBoundaryFlat4DContinuumPromoted ≡ false
toeBoundaryFlat4DContinuumPromotedIsFalse =
  YMTOE.toePublishedRGDoesNotPromoteContinuum

toeBoundaryClayYangMillsPromoted : Bool
toeBoundaryClayYangMillsPromoted =
  YMTOE.toeClayYangMillsPromoted

toeBoundaryClayYangMillsPromotedIsFalse :
  toeBoundaryClayYangMillsPromoted ≡ false
toeBoundaryClayYangMillsPromotedIsFalse =
  YMTOE.toeClayYangMillsPromotedIsFalse

ymBalabanRGPhysicalBoundaryTOECompilerLevel : ProofLevel
ymBalabanRGPhysicalBoundaryTOECompilerLevel = machineChecked
