{-# OPTIONS --safe #-}
module DASHI.Unified.FleetFormalGapTargetTOEExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)

import DASHI.Interop.PNFSpectralCoordinateRebuildability as Rebuild
import DASHI.Interop.PNFSpectralNumericABICore as Numeric
import DASHI.Interop.PNFResidualFieldInvariants as Residual
import DASHI.Planning.PlanningPNFClaimBoundaryExact as Planning
import DASHI.Promotion.ObligationIndex as Obligation
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as ParetoSnowball
import DASHI.Unified.BalabanRGTOERegression as BalabanRG
import DASHI.Physics.Closure.NSABCDConcentratedCompletionCutExact as NS
import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologySourceAtlasExact as QMSources
import DASHI.Core.RelationalTrialecticDisambiguationExact as Disambiguation

------------------------------------------------------------------------
-- Fleet R4/R5 selection boundary.
--
-- External execution context:
--   chboishabba/ITIR-suite
--   COMPACTIFIED_CONTEXT.md
--   docs/planning/fleet_topical_pnf_world_model_convergence_20261027.md
--
-- The external receipt reports an R4 numeric spectral reduction and an R5
-- formal-AST subtraction.  This module does not re-run either producer.
-- It does not promote the external counts or eigenvalues into theorem truth.
-- It only binds the reported planning frontier to existing DASHI owners.
------------------------------------------------------------------------

record FleetFormalGapTargetReceipt : Set where
  constructor fleet-formal-gap-target-receipt
  field
    externalSourceRepository : String
    externalSourceSurface : String
    spectralNumericABI : String
    spectralParityHash : String
    sourceFormalStemCount : Nat
    dischargedCoreKnowledgeFibres : Nat
    polarityContradictionGaps : Nat
    unformalisedFormalGaps : Nat
    macroscopicEigenMotifCount : Nat
    firstEigenvalueLabel : String
    secondEigenvalueLabel : String
    thirdEigenvalueLabel : String
    targetOnlyUnformalisedFormalGaps : Bool
    dischargedFibresRemainDischarged : Bool
    contradictionGapsRemainSeparate : Bool
    eigenvalueMagnitudeCreatesProofAuthority : Bool
    spectralLabelsIdentifyTheoremOwners : Bool
    externalCountCreatesFormalProof : Bool
    externalPlanningTextCreatesFormalResidual : Bool
    metaIntrospectorReferenceRepos : String
    metaIntrospectorProofBorrowed : Bool
    metaIntrospectorAttributionPreserved : Bool
    esdSurfaceEdited : Bool

open FleetFormalGapTargetReceipt public

canonicalFleetFormalGapTargetReceipt : FleetFormalGapTargetReceipt
canonicalFleetFormalGapTargetReceipt =
  fleet-formal-gap-target-receipt
    "chboishabba/ITIR-suite"
    "COMPACTIFIED_CONTEXT.md; docs/planning/fleet_topical_pnf_world_model_convergence_20261027.md"
    "itir.pnf.spectral_numeric_abi.v0_2"
    "6853373e81e551aea8fca490ce2ad9f5264664d49bde8804edfc4e98e7517799"
    13344
    584
    44
    58
    3
    "lambda1=74.5526; external planning label: Balaban RG"
    "lambda2=18.8350; external planning label: NS BM2"
    "lambda3=5.5865; external planning label: Quantum Mereology"
    true
    true
    true
    false
    false
    false
    false
    "meta-introspector/zkperf; meta-introspector/zos-server; meta-introspector/erdfa-py; meta-introspector/aristotle-cli-rs"
    false
    true
    false

------------------------------------------------------------------------
-- Exact values of the recorded external planning receipt.
-- These equalities validate this DASHI wrapper only.
-- They do not validate the external producer run.
------------------------------------------------------------------------

fleetRecordedDischargedCountIs584 :
  dischargedCoreKnowledgeFibres canonicalFleetFormalGapTargetReceipt ≡ 584
fleetRecordedDischargedCountIs584 = refl

fleetRecordedContradictionCountIs44 :
  polarityContradictionGaps canonicalFleetFormalGapTargetReceipt ≡ 44
fleetRecordedContradictionCountIs44 = refl

fleetRecordedUnformalisedGapCountIs58 :
  unformalisedFormalGaps canonicalFleetFormalGapTargetReceipt ≡ 58
fleetRecordedUnformalisedGapCountIs58 = refl

fleetRecordedMacroscopicMotifCountIs3 :
  macroscopicEigenMotifCount canonicalFleetFormalGapTargetReceipt ≡ 3
fleetRecordedMacroscopicMotifCountIs3 = refl

fleetTargetsOnlyUnformalisedFormalGaps :
  targetOnlyUnformalisedFormalGaps canonicalFleetFormalGapTargetReceipt ≡ true
fleetTargetsOnlyUnformalisedFormalGaps = refl

fleetDoesNotRetargetDischargedFibres :
  dischargedFibresRemainDischarged canonicalFleetFormalGapTargetReceipt ≡ true
fleetDoesNotRetargetDischargedFibres = refl

fleetKeepsContradictionsSeparate :
  contradictionGapsRemainSeparate canonicalFleetFormalGapTargetReceipt ≡ true
fleetKeepsContradictionsSeparate = refl

------------------------------------------------------------------------
-- Existing discharged motif owners.
--
-- These references prevent spectral planning labels from becoming new theorem
-- owners. They do not assert that the external eigenvectors identify these
-- modules by theorem.
------------------------------------------------------------------------

BalabanDischargedOwnerReceipt : Set
BalabanDischargedOwnerReceipt =
  BalabanRG.BalabanRGTOEReceipt

fleetBalabanDischargedOwnerReceipt :
  BalabanDischargedOwnerReceipt
fleetBalabanDischargedOwnerReceipt =
  BalabanRG.canonicalBalabanRGTOEReceipt

fleetNSPhysicalM2SummationCompilerStatus :
  Bool
fleetNSPhysicalM2SummationCompilerStatus =
  NS.bSamplewiseM2SummationCompilerClosed

fleetNSM2ToR568CompilerStatus :
  Bool
fleetNSM2ToR568CompilerStatus =
  NS.bM2ToR568CompilerClosed

QuantumMereologyDischargedBoundary : Set
QuantumMereologyDischargedBoundary =
  QM.QuantumMereologyBoundary

fleetQuantumMereologyBoundary :
  QuantumMereologyDischargedBoundary
fleetQuantumMereologyBoundary =
  QM.canonicalQuantumMereologyBoundary

QuantumMereologyAttributionBoundary : Set
QuantumMereologyAttributionBoundary =
  QMSources.QuantumMereologyAttributionBoundary

fleetQuantumMereologyAttributionBoundary :
  QuantumMereologyAttributionBoundary
fleetQuantumMereologyAttributionBoundary =
  QMSources.canonicalQuantumMereologyAttributionBoundary

fleetSpectralLabelDoesNotIdentifyTheoremOwner :
  spectralLabelsIdentifyTheoremOwners canonicalFleetFormalGapTargetReceipt
  ≡ false
fleetSpectralLabelDoesNotIdentifyTheoremOwner = refl

------------------------------------------------------------------------
-- Reused canonical proof and receipt owners.
------------------------------------------------------------------------

fleetCoordinateRebuildabilityReceipt :
  Rebuild.PNFSpectralCoordinateRebuildabilityReceipt
fleetCoordinateRebuildabilityReceipt =
  Rebuild.canonicalPNFSpectralCoordinateRebuildabilityReceipt

fleetNumericABIReceipt :
  Numeric.PNFSpectralNumericABICoreReceipt
fleetNumericABIReceipt =
  Numeric.canonicalPNFSpectralNumericABICoreReceipt

fleetResidualInvariantReceipt :
  Residual.PNFResidualFieldInvariantReceipt
fleetResidualInvariantReceipt =
  Residual.canonicalPNFResidualFieldInvariantReceipt

fleetPlanningBoundary :
  Planning.PNFPlanningAdapterBoundary
fleetPlanningBoundary =
  Planning.canonicalPNFPlanningAdapterBoundary

fleetPromotionObligationIndex :
  Obligation.UnifiedPromotionObligationIndex
fleetPromotionObligationIndex =
  Obligation.canonicalUnifiedPromotionObligationIndex

fleetVectorCoordinateDoesNotCreateTruth :
  Rebuild.vectorCoordinateIsTruth ≡ false
fleetVectorCoordinateDoesNotCreateTruth =
  Rebuild.vectorCoordinateTruthFalse

PlanningSourceTextFormalResidualFlag : Set
PlanningSourceTextFormalResidualFlag =
  Planning.PNFPlanningAdapterBoundary.sourceTextAloneCreatesFormalResidual
    Planning.canonicalPNFPlanningAdapterBoundary
  ≡ false

fleetPlanningTextDoesNotCreateFormalResidual :
  PlanningSourceTextFormalResidualFlag
fleetPlanningTextDoesNotCreateFormalResidual =
  Planning.PNFPlanningAdapterBoundary.sourceTextAloneCreatesFormalResidualIsFalse
    Planning.canonicalPNFPlanningAdapterBoundary

------------------------------------------------------------------------
-- Exact non-promotion gates for the external fleet selection.
--
-- These are facts about the canonical receipt fields. They are not vacuous
-- empty-type eliminators and they do not convert external planning data into
-- theorem authority.
------------------------------------------------------------------------

fleetEigenPriorityDoesNotCreateProof :
  eigenvalueMagnitudeCreatesProofAuthority canonicalFleetFormalGapTargetReceipt
  ≡ false
fleetEigenPriorityDoesNotCreateProof = refl

fleetExternalCountDoesNotCreateFormalDischarge :
  externalCountCreatesFormalProof canonicalFleetFormalGapTargetReceipt
  ≡ false
fleetExternalCountDoesNotCreateFormalDischarge = refl

fleetDischargedFibresRemainOutOfTarget :
  dischargedFibresRemainDischarged canonicalFleetFormalGapTargetReceipt
  ≡ true
fleetDischargedFibresRemainOutOfTarget = refl

fleetContradictionGapsRemainSeparate :
  contradictionGapsRemainSeparate canonicalFleetFormalGapTargetReceipt
  ≡ true
fleetContradictionGapsRemainSeparate = refl

fleetExternalPlanningTextDoesNotCreateFormalResidual :
  externalPlanningTextCreatesFormalResidual canonicalFleetFormalGapTargetReceipt
  ≡ false
fleetExternalPlanningTextDoesNotCreateFormalResidual = refl

------------------------------------------------------------------------
-- Typed non-promotion gates for the fleet planning frontier.
--
-- The Boolean receipt fields remain audit facts.
-- These constructorless types give consumers exact fail-closed gates.
-- They do not validate the external producer run.
------------------------------------------------------------------------

data FleetEigenPriorityCreatesProof : Set where

data FleetExternalCountCreatesFormalDischarge : Set where

data FleetDischargedFibreRetargetPermission : Set where

data FleetContradictionGapReclassificationPermission : Set where

fleetEigenPriorityPromotionImpossible :
  FleetEigenPriorityCreatesProof → ⊥
fleetEigenPriorityPromotionImpossible ()

fleetExternalCountPromotionImpossible :
  FleetExternalCountCreatesFormalDischarge → ⊥
fleetExternalCountPromotionImpossible ()

fleetDischargedFibresCannotBeRetargetedByThisBoundary :
  FleetDischargedFibreRetargetPermission → ⊥
fleetDischargedFibresCannotBeRetargetedByThisBoundary ()

fleetContradictionsCannotBeRelabelledAsFormalGaps :
  FleetContradictionGapReclassificationPermission → ⊥
fleetContradictionsCannotBeRelabelledAsFormalGaps ()

------------------------------------------------------------------------
-- Reuse the existing O/R/C/S/L/P/G/F process carrier.
------------------------------------------------------------------------

canonicalFleetFormalGapZKPFrame : ParetoSnowball.TOEZKPFrame
canonicalFleetFormalGapZKPFrame =
  ParetoSnowball.toe-zkp-frame
    "target only the externally reported 58 unformalised formal gaps after the 584 discharged fibres remain excluded"
    "reuse canonical PNF spectral, residual, planning, obligation, Balaban and Ibrahim owners"
    "bind one external fleet planning receipt to existing owners; add no duplicate theorem owner"
    "spectral rank, external counts, planning labels and contradiction classes do not create proof authority or formal discharge"
    "one disjoint fleet residual-selection normalization lane"
    "the R4/R5 receipt is external context; canonical DASHI owners remain proof authority; ESD surfaces are read-only"
    "ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma and C4/PlantUML are process lenses only; meta-introspector attribution remains separate"
    "TOE consumers expose the 58-gap target boundary while the 584 discharged fibres and 44 contradiction gaps remain outside that target"
    "reuse/duplicate search, exact-branch read-back, trust-escape scan, ESD diff scan and owner-alias validation"
    false
    false
    false
    false


------------------------------------------------------------------------
-- Direct source-owned PNF non-promotion gates.
--
-- The fleet receipt is external planning context. These theorem gates come
-- from the canonical DASHI PNF owners and remain the proof authority.
------------------------------------------------------------------------

NonRebuildableCoordinatePromotion : Set
NonRebuildableCoordinatePromotion =
  Rebuild.NonRebuildablePromotion

VectorSpectralAuthorityPromotion : Set
VectorSpectralAuthorityPromotion =
  Rebuild.VectorAuthorityPromotion

SpectralNumericABIPromotion : Set
SpectralNumericABIPromotion =
  Numeric.PNFSpectralNumericABIPromotion

ResidualFieldPromotion : Set
ResidualFieldPromotion =
  Residual.PNFResidualFieldInvariantPromotion

fleetNonRebuildableCoordinatePromotionImpossible :
  NonRebuildableCoordinatePromotion → ⊥
fleetNonRebuildableCoordinatePromotionImpossible =
  Rebuild.nonRebuildablePromotionImpossible

fleetVectorSpectralAuthorityPromotionImpossible :
  VectorSpectralAuthorityPromotion → ⊥
fleetVectorSpectralAuthorityPromotionImpossible =
  Rebuild.vectorAuthorityPromotionImpossible

fleetSpectralNumericABIPromotionImpossible :
  SpectralNumericABIPromotion → ⊥
fleetSpectralNumericABIPromotionImpossible =
  Numeric.pnfSpectralNumericABIPromotionImpossible

fleetResidualFieldPromotionImpossible :
  ResidualFieldPromotion → ⊥
fleetResidualFieldPromotionImpossible =
  Residual.pnfResidualFieldInvariantPromotionImpossible

fleetVectorCoordinateTruthStillFalse :
  Rebuild.vectorCoordinateIsTruth ≡ false
fleetVectorCoordinateTruthStillFalse =
  Rebuild.vectorCoordinateTruthFalse

fleetVectorCoordinateSupportStillFalse :
  Rebuild.vectorCoordinateIsCommittedSupport ≡ false
fleetVectorCoordinateSupportStillFalse =
  Rebuild.vectorCoordinateCommittedSupportFalse

fleetVectorCoordinateAdmissibilityStillFalse :
  Rebuild.vectorCoordinateIsAdmissibility ≡ false
fleetVectorCoordinateAdmissibilityStillFalse =
  Rebuild.vectorCoordinateAdmissibilityFalse

fleetTextFallbackAuthorityStillFalse :
  Rebuild.textFallbackIsCoordinateAuthority ≡ false
fleetTextFallbackAuthorityStillFalse =
  Rebuild.textFallbackCoordinateAuthorityFalse


------------------------------------------------------------------------
-- Exact ordinal cut for the recorded R5 partition.
--
-- These Fin carriers encode only the three recorded cardinalities.
-- They do not identify persisted rows.
-- They do not manufacture names for the 58 formal-gap rows.
-- Downstream proof work ranges over exactly 58 target slots.
-- The 584 discharged slots and 44 contradiction slots remain separate.
------------------------------------------------------------------------

FleetDischargedOrdinal : Set
FleetDischargedOrdinal = Fin 584

FleetContradictionOrdinal : Set
FleetContradictionOrdinal = Fin 44

FleetFormalGapOrdinal : Set
FleetFormalGapOrdinal = Fin 58

fleetFormalGapOrdinalCount : Nat
fleetFormalGapOrdinalCount =
  unformalisedFormalGaps canonicalFleetFormalGapTargetReceipt

fleetFormalGapOrdinalCountIs58 :
  fleetFormalGapOrdinalCount ≡ 58
fleetFormalGapOrdinalCountIs58 =
  fleetRecordedUnformalisedGapCountIs58

fleetDischargedOrdinalCount : Nat
fleetDischargedOrdinalCount =
  dischargedCoreKnowledgeFibres canonicalFleetFormalGapTargetReceipt

fleetDischargedOrdinalCountIs584 :
  fleetDischargedOrdinalCount ≡ 584
fleetDischargedOrdinalCountIs584 =
  fleetRecordedDischargedCountIs584

fleetContradictionOrdinalCount : Nat
fleetContradictionOrdinalCount =
  polarityContradictionGaps canonicalFleetFormalGapTargetReceipt

fleetContradictionOrdinalCountIs44 :
  fleetContradictionOrdinalCount ≡ 44
fleetContradictionOrdinalCountIs44 =
  fleetRecordedContradictionCountIs44

fleetOrdinalCarriesPersistedRowIdentity : Bool
fleetOrdinalCarriesPersistedRowIdentity = false

fleetOrdinalCarriesPersistedRowIdentityIsFalse :
  fleetOrdinalCarriesPersistedRowIdentity ≡ false
fleetOrdinalCarriesPersistedRowIdentityIsFalse = refl

FleetSharedCardinalityCreatesIdentity : Set
FleetSharedCardinalityCreatesIdentity =
  Disambiguation.SharedCardinalityCreatesIdentity

fleetSharedCardinalityDoesNotCreateIdentity :
  FleetSharedCardinalityCreatesIdentity → ⊥
fleetSharedCardinalityDoesNotCreateIdentity =
  Disambiguation.sharedCardinalityDoesNotCreateIdentity

------------------------------------------------------------------------
-- ZKP cut receipt.
--
-- O: Fleet R5 target partition.
-- R: Reuse the recorded 584/44/58 receipt and identity firewall.
-- C: Add exact ordinal carriers only.
-- S: Names, row identity, theorem authority, and discharge do not follow.
-- L: Fleet receipt -> ordinal cut -> TOE consumers.
-- P: The recorded partition is the precondition.
-- G: Attribution and ESD boundaries stay unchanged.
-- F: Per-row dispatch still requires a checked row-identity attachment.
------------------------------------------------------------------------

record FleetR5OrdinalCutReceipt : Set₁ where
  constructor fleet-r5-ordinal-cut-receipt
  field
    dischargedOrdinal : Set
    dischargedOrdinalIsCanonical :
      dischargedOrdinal ≡ FleetDischargedOrdinal

    contradictionOrdinal : Set
    contradictionOrdinalIsCanonical :
      contradictionOrdinal ≡ FleetContradictionOrdinal

    formalGapOrdinal : Set
    formalGapOrdinalIsCanonical :
      formalGapOrdinal ≡ FleetFormalGapOrdinal

    targetCount : Nat
    targetCountIs58 : targetCount ≡ 58

    dischargedCount : Nat
    dischargedCountIs584 : dischargedCount ≡ 584

    contradictionCount : Nat
    contradictionCountIs44 : contradictionCount ≡ 44

    ordinalCarriesPersistedIdentity : Bool
    ordinalCarriesPersistedIdentityIsFalse :
      ordinalCarriesPersistedIdentity ≡ false

    sharedCardinalityIdentityFirewall :
      FleetSharedCardinalityCreatesIdentity → ⊥

open FleetR5OrdinalCutReceipt public

canonicalFleetR5OrdinalCutReceipt : FleetR5OrdinalCutReceipt
canonicalFleetR5OrdinalCutReceipt = record
  { dischargedOrdinal = FleetDischargedOrdinal
  ; dischargedOrdinalIsCanonical = refl
  ; contradictionOrdinal = FleetContradictionOrdinal
  ; contradictionOrdinalIsCanonical = refl
  ; formalGapOrdinal = FleetFormalGapOrdinal
  ; formalGapOrdinalIsCanonical = refl
  ; targetCount = fleetFormalGapOrdinalCount
  ; targetCountIs58 = fleetFormalGapOrdinalCountIs58
  ; dischargedCount = fleetDischargedOrdinalCount
  ; dischargedCountIs584 = fleetDischargedOrdinalCountIs584
  ; contradictionCount = fleetContradictionOrdinalCount
  ; contradictionCountIs44 = fleetContradictionOrdinalCountIs44
  ; ordinalCarriesPersistedIdentity =
      fleetOrdinalCarriesPersistedRowIdentity
  ; ordinalCarriesPersistedIdentityIsFalse =
      fleetOrdinalCarriesPersistedRowIdentityIsFalse
  ; sharedCardinalityIdentityFirewall =
      fleetSharedCardinalityDoesNotCreateIdentity
  }
