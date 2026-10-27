module DASHI.Physics.YangMills.YangMillsPlaquetteTOEBridgeExact where

------------------------------------------------------------------------
-- ZKP O / R / C / S / L / P / G / F
--
-- O. Objective.
-- Connect the exact finite Wilson-plaquette theorem owners and exact
-- Yang-Mills non-promotion theorems to the focused DASHI TOE graph.
--
-- R. Reuse.
-- Reuse SUNWilsonAction for finite SU(N) gauge invariance.
-- Reuse BalabanSU2WilsonPlaquetteSecondJetExact for the exact local Hessian.
-- Reuse BalabanP33PhysicalFlatWilsonCurlIdentificationExact for the physical
-- flat Wilson/curl identity.
-- Reuse BalabanPlaquetteCrossChargeZeroFloorNoGoExact for the exact zero-field
-- cross-charge theorem.
-- Reuse BalabanClayT4BetaNormalizationConventionExact for the exact rational
-- one-loop convention and its still-conditional physical coefficient seam.
-- Reuse YMClayFullPhysicalFormalismExact for the current Route-S and Level-2
-- Pareto firewalls.
-- Reuse YangMillsMassGapBoundary and YMClayPromotionBoundary for exact
-- non-promotion theorems.
--
-- C. Concrete result.
-- This file is a normalized import/projection bridge.
-- It adds no second plaquette, RG, OS, Hamiltonian, or Clay ontology.
--
-- S. Preconditions and invariants.
-- The finite theorem owners remain authoritative.
-- A finite plaquette theorem does not imply a continuum theorem.
-- A zero-field cross-charge theorem forbids an unconditional positive floor
-- on a carrier that still contains the zero field.
-- A rational beta convention does not identify the physical RG coefficient.
-- A mass-gap target is not a promoted mass-gap theorem.
-- A TOE import edge never promotes Clay Yang-Mills.
--
-- L. Lane.
-- This lane owns only Yang-Mills plaquette-to-TOE normalization.
-- ESD and digital_esd surfaces are import-only and are not edited.
-- Meta-introspector repositories remain process/tooling references only.
--
-- P. Postconditions.
-- TOE consumers can reach the exact finite plaquette theorem levels.
-- TOE consumers can reach exact mass-gap and Clay non-promotion proofs.
-- TOE consumers can reach the current Route-S/Level-2 non-promotion firewalls.
--
-- G. Governance.
-- One result has one canonical theorem owner.
-- Original mathematical attribution stays in the imported owner modules.
-- This bridge makes no standards-certification claim.
--
-- F. Verification.
-- Source read-back must find each import and theorem below.
-- Exact-head Agda kernel certification remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.SUNWilsonAction as WilsonAction
import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact as Jet
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanPlaquetteCrossChargeZeroFloorNoGoExact as ZeroFloor
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.YMClayFullPhysicalFormalismExact as Full
import DASHI.Physics.Closure.YangMillsMassGapBoundary as GapBoundary
import DASHI.Physics.Closure.YMClayPromotionBoundary as Promotion

------------------------------------------------------------------------
-- Exact finite Wilson/plaquette owners.
------------------------------------------------------------------------

toeFiniteSUNWilsonGaugeInvarianceLevel : ProofLevel
toeFiniteSUNWilsonGaugeInvarianceLevel =
  WilsonAction.sunWilsonActionGaugeInvarianceLevel

toeSinglePlaquetteSecondVariationLevel : ProofLevel
toeSinglePlaquetteSecondVariationLevel =
  Jet.singlePlaquetteWilsonSecondVariationLevel

toePhysicalFlatWilsonCurlIdentificationLevel : ProofLevel
toePhysicalFlatWilsonCurlIdentificationLevel =
  Flat.physicalFlatWilsonCurlIdentificationLevel

toeZeroPhysicalFieldCrossChargeLevel : ProofLevel
toeZeroPhysicalFieldCrossChargeLevel =
  ZeroFloor.zeroPhysicalFieldHasZeroCrossChargeLevel

toeZeroPhysicalFieldCrossCharge :
  ∀ left right site →
  Incidence.plaquetteCrossCharge
    ZeroFloor.zeroPhysicalField left right site
  ≡ 0ℚ
toeZeroPhysicalFieldCrossCharge =
  ZeroFloor.zeroPlaquetteCrossCharge

------------------------------------------------------------------------
-- Exact beta convention and physical identification boundary.
------------------------------------------------------------------------

toePureYMWilsonConventionLedgerLevel : ProofLevel
toePureYMWilsonConventionLedgerLevel =
  Beta.pureYMWilsonConventionLedgerLevel

toePhysicalPlaquetteCoefficientIdentificationLevel : ProofLevel
toePhysicalPlaquetteCoefficientIdentificationLevel =
  Beta.physicalPlaquetteCoefficientIdentificationLevel

------------------------------------------------------------------------
-- Current Route-S and Level-2 Pareto firewalls.
------------------------------------------------------------------------

toeDirectSourceOSIsLeastPrivilegeMassGapRoute : Bool
toeDirectSourceOSIsLeastPrivilegeMassGapRoute =
  Full.directSourceOSIsLeastPrivilegeMassGapRoute

toeDirectSourceOSIsLeastPrivilegeMassGapRouteIsTrue :
  toeDirectSourceOSIsLeastPrivilegeMassGapRoute ≡ true
toeDirectSourceOSIsLeastPrivilegeMassGapRouteIsTrue =
  Full.directSourceOSIsLeastPrivilegeMassGapRouteIsTrue

toeRouteSRequiresDenseL2Normalization : Bool
toeRouteSRequiresDenseL2Normalization =
  Full.routeSRequiresDenseL2Normalization

toeRouteSRequiresDenseL2NormalizationIsFalse :
  toeRouteSRequiresDenseL2Normalization ≡ false
toeRouteSRequiresDenseL2NormalizationIsFalse =
  Full.routeSRequiresDenseL2NormalizationIsFalse


toeRouteSH1HasOneTheoremBearingField : Bool
toeRouteSH1HasOneTheoremBearingField =
  Full.routeSH1HasOneTheoremBearingField

toeRouteSH1HasOneTheoremBearingFieldIsTrue :
  toeRouteSH1HasOneTheoremBearingField ≡ true
toeRouteSH1HasOneTheoremBearingFieldIsTrue =
  Full.routeSH1HasOneTheoremBearingFieldIsTrue

toeRouteSH1RequiresHistoricalPublishedWrapper : Bool
toeRouteSH1RequiresHistoricalPublishedWrapper =
  Full.routeSH1RequiresHistoricalPublishedWrapper

toeRouteSH1RequiresHistoricalPublishedWrapperIsFalse :
  toeRouteSH1RequiresHistoricalPublishedWrapper ≡ false
toeRouteSH1RequiresHistoricalPublishedWrapperIsFalse =
  Full.routeSH1RequiresHistoricalPublishedWrapperIsFalse

toeRouteSH1ToR387RequiresSourceEnvelope : Bool
toeRouteSH1ToR387RequiresSourceEnvelope =
  Full.routeSH1ToR387RequiresSourceEnvelope

toeRouteSH1ToR387RequiresSourceEnvelopeIsFalse :
  toeRouteSH1ToR387RequiresSourceEnvelope ≡ false
toeRouteSH1ToR387RequiresSourceEnvelopeIsFalse =
  Full.routeSH1ToR387RequiresSourceEnvelopeIsFalse

toeD1NewAnalyticInequalityRequired : Bool
toeD1NewAnalyticInequalityRequired =
  Full.d1NewAnalyticInequalityRequired

toeD1NewAnalyticInequalityRequiredIsFalse :
  toeD1NewAnalyticInequalityRequired ≡ false
toeD1NewAnalyticInequalityRequiredIsFalse =
  Full.d1NewAnalyticInequalityRequiredIsFalse

toeD2SecondMixingMapRequired : Bool
toeD2SecondMixingMapRequired =
  Full.d2SecondMixingMapRequired

toeD2SecondMixingMapRequiredIsFalse :
  toeD2SecondMixingMapRequired ≡ false
toeD2SecondMixingMapRequiredIsFalse =
  Full.d2SecondMixingMapRequiredIsFalse


toeD2BareTransportABIPaysPhysicalMixing : Bool
toeD2BareTransportABIPaysPhysicalMixing =
  Full.d2BareTransportABIPaysPhysicalMixing

toeD2BareTransportABIPaysPhysicalMixingIsFalse :
  toeD2BareTransportABIPaysPhysicalMixing ≡ false
toeD2BareTransportABIPaysPhysicalMixingIsFalse =
  Full.d2BareTransportABIPaysPhysicalMixingIsFalse


toeD2PublishedSourceEntryPaysInsertionNaturality : Bool
toeD2PublishedSourceEntryPaysInsertionNaturality =
  Full.d2PublishedSourceEntryPaysInsertionNaturality

toeD2PublishedSourceEntryPaysInsertionNaturalityIsFalse :
  toeD2PublishedSourceEntryPaysInsertionNaturality ≡ false
toeD2PublishedSourceEntryPaysInsertionNaturalityIsFalse =
  Full.d2PublishedSourceEntryPaysInsertionNaturalityIsFalse

toeD2PublishedSourceEntryDeterminesCompositeInsertion : Bool
toeD2PublishedSourceEntryDeterminesCompositeInsertion =
  Full.d2PublishedSourceEntryDeterminesCompositeInsertion

toeD2PublishedSourceEntryDeterminesCompositeInsertionIsFalse :
  toeD2PublishedSourceEntryDeterminesCompositeInsertion ≡ false
toeD2PublishedSourceEntryDeterminesCompositeInsertionIsFalse =
  Full.d2PublishedSourceEntryDeterminesCompositeInsertionIsFalse

toeD2IndependentPhysicalOneStepRecurrenceRequired : Bool
toeD2IndependentPhysicalOneStepRecurrenceRequired =
  Full.d2IndependentPhysicalOneStepRecurrenceRequired

toeD2IndependentPhysicalOneStepRecurrenceRequiredIsFalse :
  toeD2IndependentPhysicalOneStepRecurrenceRequired ≡ false
toeD2IndependentPhysicalOneStepRecurrenceRequiredIsFalse =
  Full.d2IndependentPhysicalOneStepRecurrenceRequiredIsFalse

toeD2SameFamilyCompositeConvergenceStillPhysical : Bool
toeD2SameFamilyCompositeConvergenceStillPhysical =
  Full.d2SameFamilyCompositeConvergenceStillPhysical

toeD2SameFamilyCompositeConvergenceStillPhysicalIsTrue :
  toeD2SameFamilyCompositeConvergenceStillPhysical ≡ true
toeD2SameFamilyCompositeConvergenceStillPhysicalIsTrue =
  Full.d2SameFamilyCompositeConvergenceStillPhysicalIsTrue

toeD2ParallelCompositeOperatorTheoryAllowed : Bool
toeD2ParallelCompositeOperatorTheoryAllowed =
  Full.d2ParallelCompositeOperatorTheoryAllowed

toeD2ParallelCompositeOperatorTheoryAllowedIsFalse :
  toeD2ParallelCompositeOperatorTheoryAllowed ≡ false
toeD2ParallelCompositeOperatorTheoryAllowedIsFalse =
  Full.d2ParallelCompositeOperatorTheoryAllowedIsFalse

toeD3PerturbationIndependentWardSequenceWouldBeTooWeak : Bool
toeD3PerturbationIndependentWardSequenceWouldBeTooWeak =
  Full.d3PerturbationIndependentWardSequenceWouldBeTooWeak

toeD3PerturbationIndependentWardSequenceWouldBeTooWeakIsTrue :
  toeD3PerturbationIndependentWardSequenceWouldBeTooWeak ≡ true
toeD3PerturbationIndependentWardSequenceWouldBeTooWeakIsTrue =
  Full.d3PerturbationIndependentWardSequenceWouldBeTooWeakIsTrue

------------------------------------------------------------------------
-- Exact non-promotion theorems.
------------------------------------------------------------------------

toeMassGapPromoted : Bool
toeMassGapPromoted =
  GapBoundary.massGapPromoted
    GapBoundary.canonicalYangMillsMassGapBoundaryReceipt

toeMassGapPromotedIsFalse :
  toeMassGapPromoted ≡ false
toeMassGapPromotedIsFalse =
  GapBoundary.massGapPromotedIsFalse
    GapBoundary.canonicalYangMillsMassGapBoundaryReceipt

toePhysicalStoneGeneratorEqualsYMHamiltonianPromoted : Bool
toePhysicalStoneGeneratorEqualsYMHamiltonianPromoted =
  GapBoundary.physicalStoneGeneratorEqualsYMHamiltonianPromoted
    GapBoundary.canonicalYangMillsMassGapBoundaryReceipt

toePhysicalStoneGeneratorEqualsYMHamiltonianPromotedIsFalse :
  toePhysicalStoneGeneratorEqualsYMHamiltonianPromoted ≡ false
toePhysicalStoneGeneratorEqualsYMHamiltonianPromotedIsFalse =
  GapBoundary.physicalStoneGeneratorEqualsYMHamiltonianPromotedIsFalse
    GapBoundary.canonicalYangMillsMassGapBoundaryReceipt

toePhysicalStoneSpectralLowerBoundPromoted : Bool
toePhysicalStoneSpectralLowerBoundPromoted =
  GapBoundary.physicalStoneSpectralLowerBoundPromoted
    GapBoundary.canonicalYangMillsMassGapBoundaryReceipt

toePhysicalStoneSpectralLowerBoundPromotedIsFalse :
  toePhysicalStoneSpectralLowerBoundPromoted ≡ false
toePhysicalStoneSpectralLowerBoundPromotedIsFalse =
  GapBoundary.physicalStoneSpectralLowerBoundPromotedIsFalse
    GapBoundary.canonicalYangMillsMassGapBoundaryReceipt

toeClayYangMillsPromoted : Bool
toeClayYangMillsPromoted =
  Promotion.clayYangMillsPromoted

toeClayYangMillsPromotedIsFalse :
  toeClayYangMillsPromoted ≡ false
toeClayYangMillsPromotedIsFalse =
  Promotion.ClayPromotionBoundary.noClayPromotion
    Promotion.clayPromotionBoundary

toeNoClayPromotionPossibleHere :
  Promotion.ClayYangMillsPromotion → ⊥
toeNoClayPromotionPossibleHere =
  Promotion.ClayPromotionBoundary.noPromotionPossibleHere
    Promotion.clayPromotionBoundary

------------------------------------------------------------------------
-- Bridge status.
------------------------------------------------------------------------

plaquetteTOEBridgeAddsNewPhysicalTheorem : Bool
plaquetteTOEBridgeAddsNewPhysicalTheorem = false

plaquetteTOEBridgeAddsNewPhysicalTheoremIsFalse :
  plaquetteTOEBridgeAddsNewPhysicalTheorem ≡ false
plaquetteTOEBridgeAddsNewPhysicalTheoremIsFalse = refl

plaquetteTOEBridgeCompilerLevel : ProofLevel
plaquetteTOEBridgeCompilerLevel = machineChecked
