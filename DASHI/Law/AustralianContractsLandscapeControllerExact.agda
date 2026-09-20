module DASHI.Law.AustralianContractsLandscapeControllerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.SensibLawNativeLegalFollowCLIExact as CLI
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as LegalFollow

------------------------------------------------------------------------
-- AUSTRALIAN CONTRACTS LANDSCAPE CONTROLLER
--
-- This is an orchestration/frontier owner for S14.  It consumes the existing
-- AustralianContractFollowTrace and keeps four kinds of residual work separate:
-- active primary-source acquisition, authority-treatment review, research
-- context expansion, and temporally inactive-but-relevant alternatives.
--
-- It is deliberately NOT a current-law oracle and NOT a complete ontology.
------------------------------------------------------------------------

data ContractLandscapeFrontierKind : Set where
  primarySourceAcquisition : ContractLandscapeFrontierKind
  authorityTreatmentReview : ContractLandscapeFrontierKind
  researchContextExpansion : ContractLandscapeFrontierKind
  temporalAlternative : ContractLandscapeFrontierKind

record ContractLandscapeWorkItem : Set where
  constructor contractLandscapeWorkItem
  field
    workReference : String
    frontierKind : ContractLandscapeFrontierKind
    semanticReference : String
    relatedReference : Maybe String
    doctrine : Maybe Contracts.ContractDoctrine
    jurisdictionReference : String
    asAtReference : String
    sourceRole : Contracts.ContractSourceRole
    sourceCitation : String
    courtReference : Maybe String
    treatment : Maybe Contracts.ContractTreatment
    activeAtAsAt : Bool
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    createsCurrentLawConclusion : Bool
    createsCurrentLawConclusionIsFalse :
      createsCurrentLawConclusion ≡ false

open ContractLandscapeWorkItem public

record AustralianContractsLandscapeWorklist : Set where
  constructor australianContractsLandscapeWorklist
  field
    rootReference : String
    asAtReference : String
    sourceFrontier : List ContractLandscapeWorkItem
    treatmentFrontier : List ContractLandscapeWorkItem
    contextFrontier : List ContractLandscapeWorkItem
    temporalFrontier : List ContractLandscapeWorkItem
    boundedSeedOnly : Bool
    boundedSeedOnlyIsTrue : boundedSeedOnly ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    createsCurrentLawConclusion : Bool
    createsCurrentLawConclusionIsFalse :
      createsCurrentLawConclusion ≡ false

open AustralianContractsLandscapeWorklist public

------------------------------------------------------------------------
-- The controller reuses existing owners.
------------------------------------------------------------------------

ContractsBoundary : Set
ContractsBoundary = Contracts.AustralianContractsFollowBoundary

contractsBoundaryPaid : ContractsBoundary
contractsBoundaryPaid =
  Contracts.canonicalAustralianContractsFollowBoundary

LegalFollowBoundary : Set
LegalFollowBoundary = LegalFollow.LegalFollowProofSearchBoundary

legalFollowBoundaryPaid : LegalFollowBoundary
legalFollowBoundaryPaid =
  LegalFollow.canonicalLegalFollowProofSearchBoundary

NativeCliBoundary : Set
NativeCliBoundary = CLI.NativeLegalFollowCliBoundary

nativeCliBoundaryPaid : NativeCliBoundary
nativeCliBoundaryPaid =
  CLI.canonicalNativeLegalFollowCliBoundary

------------------------------------------------------------------------
-- Concrete Queensland temporal-slice fixture.
--
-- This is deliberately a narrow parity fixture, not a complete QLD contract
-- landscape.  It mirrors the Rust 2026 worklist invariant: successor s 68 is
-- active source work while predecessor s 55 remains an explicit temporal
-- alternative.
------------------------------------------------------------------------

qld1974Section55Node : Contracts.ContractTraceNode
qld1974Section55Node =
  Contracts.contractTraceNode
    "legislation:qld:property-law-act-1974:s55"
    "Property Law Act 1974 (Qld) s 55"
    Contracts.legislationNode
    (just Contracts.privity)
    "AU-QLD"
    nothing
    nothing
    nothing
    (just "2025-07-31")
    Contracts.primaryLegislation
    Contracts.official
    "Property Law Act 1974 (Qld) s 55"
    true refl
    false refl

qld2023Section68Node : Contracts.ContractTraceNode
qld2023Section68Node =
  Contracts.contractTraceNode
    "legislation:qld:property-law-act-2023:s68"
    "Property Law Act 2023 (Qld) s 68"
    Contracts.legislationNode
    (just Contracts.privity)
    "AU-QLD"
    nothing
    (just "2025-08-01")
    (just "2025-08-01")
    nothing
    Contracts.primaryLegislation
    Contracts.official
    "Property Law Act 2023 (Qld) s 68"
    true refl
    false refl

qld2026ActiveSourceWork : ContractLandscapeWorkItem
qld2026ActiveSourceWork =
  contractLandscapeWorkItem
    "contracts:landscape:source:legislation:qld:property-law-act-2023:s68"
    primarySourceAcquisition
    "legislation:qld:property-law-act-2023:s68"
    nothing
    (just Contracts.privity)
    "AU-QLD"
    "2026-09-20"
    Contracts.primaryLegislation
    "Property Law Act 2023 (Qld) s 68"
    nothing
    nothing
    true
    true refl
    false refl
    false refl

qld2026TemporalAlternativeWork : ContractLandscapeWorkItem
qld2026TemporalAlternativeWork =
  contractLandscapeWorkItem
    "contracts:landscape:temporal:legislation:qld:property-law-act-1974:s55"
    temporalAlternative
    "legislation:qld:property-law-act-1974:s55"
    nothing
    (just Contracts.privity)
    "AU-QLD"
    "2026-09-20"
    Contracts.primaryLegislation
    "Property Law Act 1974 (Qld) s 55"
    nothing
    nothing
    false
    true refl
    false refl
    false refl

doctrineExpansionWork :
  String →
  String →
  String →
  Contracts.ContractDoctrine →
  ContractLandscapeWorkItem
doctrineExpansionWork workRef semanticRef sourceRef doctrine =
  contractLandscapeWorkItem
    workRef
    researchContextExpansion
    semanticRef
    (just "landscape:au:contract-law")
    (just doctrine)
    "AU"
    "2026-09-20"
    Contracts.researchIndex
    sourceRef
    nothing
    nothing
    true
    true refl
    false refl
    false refl

constructionExpansionWork : ContractLandscapeWorkItem
constructionExpansionWork =
  doctrineExpansionWork
    "contracts:landscape:context:doctrine:construction"
    "doctrine:au:contract:construction"
    "doctrine-query:construction"
    Contracts.construction

unconscionabilityExpansionWork : ContractLandscapeWorkItem
unconscionabilityExpansionWork =
  doctrineExpansionWork
    "contracts:landscape:context:doctrine:unconscionability"
    "doctrine:au:contract:unconscionability"
    "doctrine-query:unconscionability"
    Contracts.unconscionability

penaltiesExpansionWork : ContractLandscapeWorkItem
penaltiesExpansionWork =
  doctrineExpansionWork
    "contracts:landscape:context:doctrine:penalties"
    "doctrine:au:contract:penalties"
    "doctrine-query:penalties"
    Contracts.penalties

consumerLawExpansionWork : ContractLandscapeWorkItem
consumerLawExpansionWork =
  doctrineExpansionWork
    "contracts:landscape:context:doctrine:consumer-law"
    "doctrine:au:contract:consumer-law"
    "doctrine-query:consumer-law"
    Contracts.consumerLaw

boundedSeedMissingDoctrineFrontier : List ContractLandscapeWorkItem
boundedSeedMissingDoctrineFrontier =
  constructionExpansionWork
    ∷ unconscionabilityExpansionWork
    ∷ penaltiesExpansionWork
    ∷ consumerLawExpansionWork
    ∷ []

qld2026TemporalSliceFixture : AustralianContractsLandscapeWorklist
qld2026TemporalSliceFixture =
  australianContractsLandscapeWorklist
    "landscape:au:contract-law"
    "2026-09-20"
    (qld2026ActiveSourceWork ∷ [])
    []
    []
    (qld2026TemporalAlternativeWork ∷ [])
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Queensland temporal non-factorability is a controller invariant, not just a
-- background theorem.  Therefore an inactive predecessor may remain visible in
-- the temporal frontier even though it is not an active acquisition target.
------------------------------------------------------------------------

qldTemporalAlternativeMustRemainRepresentable :
  NF.FactorsThrough
    Contracts.coarsePrivityProjection
    Contracts.operativePrivityRoute
  → ⊥
qldTemporalAlternativeMustRemainRepresentable =
  Contracts.coarseDoctrineLabelCannotRecoverAsAtRoute

data ContractLandscapeAcquisitionOutcome : Set where
  sourceResolved : ContractLandscapeAcquisitionOutcome
  sourceResidual : ContractLandscapeAcquisitionOutcome

record ContractLandscapeAcquisitionReceipt : Set where
  constructor contractLandscapeAcquisitionReceipt
  field
    workReference : String
    semanticReference : String
    outcome : ContractLandscapeAcquisitionOutcome
    sourceRevisionReference : Maybe String
    sectionReference : Maybe String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    createsCurrentLawConclusion : Bool
    createsCurrentLawConclusionIsFalse :
      createsCurrentLawConclusion ≡ false
    sectionReceiptPaid : Bool
    sectionReceiptPaidIsFalse : sectionReceiptPaid ≡ false
    treatmentReviewPaid : Bool
    treatmentReviewPaidIsFalse : treatmentReviewPaid ≡ false
    missingSourceIsNegativeLegalEvidence : Bool
    missingSourceIsNegativeLegalEvidenceIsFalse :
      missingSourceIsNegativeLegalEvidence ≡ false

open ContractLandscapeAcquisitionReceipt public

------------------------------------------------------------------------
-- No-collapse laws for S14 orchestration.
------------------------------------------------------------------------

data SourceAcquisitionAutomaticallyTreatment : Set where
data SourceAcquisitionAutomaticallyCurrentLaw : Set where
data TreatmentSeedAutomaticallyReviewedTreatment : Set where
data ContextExpansionAutomaticallyPrimaryAuthority : Set where
data InactiveTemporalAlternativeMayBeDiscarded : Set where
data BoundedSeedAutomaticallyCompleteLandscape : Set where
data LandscapeControllerAutomaticallyLegalAuthority : Set where
data MissingLandscapeSourceAutomaticallyNegativeEvidence : Set where
data ActAcquisitionAutomaticallyPaysSection : Set where
data SourceReceiptAutomaticallyPaysTreatmentReview : Set where

sourceAcquisitionDoesNotCreateTreatment :
  SourceAcquisitionAutomaticallyTreatment → ⊥
sourceAcquisitionDoesNotCreateTreatment ()

sourceAcquisitionDoesNotCreateCurrentLaw :
  SourceAcquisitionAutomaticallyCurrentLaw → ⊥
sourceAcquisitionDoesNotCreateCurrentLaw ()

seedTreatmentDoesNotBecomeReviewedTreatment :
  TreatmentSeedAutomaticallyReviewedTreatment → ⊥
seedTreatmentDoesNotBecomeReviewedTreatment ()

contextExpansionDoesNotBecomePrimaryAuthority :
  ContextExpansionAutomaticallyPrimaryAuthority → ⊥
contextExpansionDoesNotBecomePrimaryAuthority ()

temporalAlternativeCannotBeErased :
  InactiveTemporalAlternativeMayBeDiscarded → ⊥
temporalAlternativeCannotBeErased ()

boundedSeedDoesNotBecomeCompleteLandscape :
  BoundedSeedAutomaticallyCompleteLandscape → ⊥
boundedSeedDoesNotBecomeCompleteLandscape ()

landscapeControllerDoesNotCreateAuthority :
  LandscapeControllerAutomaticallyLegalAuthority → ⊥
landscapeControllerDoesNotCreateAuthority ()

missingLandscapeSourceDoesNotBecomeNegativeEvidence :
  MissingLandscapeSourceAutomaticallyNegativeEvidence → ⊥
missingLandscapeSourceDoesNotBecomeNegativeEvidence ()

actAcquisitionDoesNotPaySection :
  ActAcquisitionAutomaticallyPaysSection → ⊥
actAcquisitionDoesNotPaySection ()

sourceReceiptDoesNotPayTreatmentReview :
  SourceReceiptAutomaticallyPaysTreatmentReview → ⊥
sourceReceiptDoesNotPayTreatmentReview ()

record AustralianContractsLandscapeControllerBoundary : Set where
  constructor australianContractsLandscapeControllerBoundary
  field
    fourFrontiersAreSeparated : Bool
    fourFrontiersAreSeparatedIsTrue :
      fourFrontiersAreSeparated ≡ true

    sourceFrontierUsesGenericLegalFollow : Bool
    sourceFrontierUsesGenericLegalFollowIsTrue :
      sourceFrontierUsesGenericLegalFollow ≡ true

    treatmentFrontierRequiresReview : Bool
    treatmentFrontierRequiresReviewIsTrue :
      treatmentFrontierRequiresReview ≡ true

    temporalAlternativesAreRetained : Bool
    temporalAlternativesAreRetainedIsTrue :
      temporalAlternativesAreRetained ≡ true

    jurisdictionAndAsAtRemainExplicit : Bool
    jurisdictionAndAsAtRemainExplicitIsTrue :
      jurisdictionAndAsAtRemainExplicit ≡ true

    boundedSeedOnly : Bool
    boundedSeedOnlyIsTrue :
      boundedSeedOnly ≡ true

    missingSeedDoctrinesBecomeContextResiduals : Bool
    missingSeedDoctrinesBecomeContextResidualsIsTrue :
      missingSeedDoctrinesBecomeContextResiduals ≡ true

    sourceAcquisitionMayLeaveResiduals : Bool
    sourceAcquisitionMayLeaveResidualsIsTrue :
      sourceAcquisitionMayLeaveResiduals ≡ true

    missingSourceIsNegativeLegalEvidence : Bool
    missingSourceIsNegativeLegalEvidenceIsFalse :
      missingSourceIsNegativeLegalEvidence ≡ false

    actAcquisitionPaysSectionReceipt : Bool
    actAcquisitionPaysSectionReceiptIsFalse :
      actAcquisitionPaysSectionReceipt ≡ false

    sourceAcquisitionPaysTreatmentReview : Bool
    sourceAcquisitionPaysTreatmentReviewIsFalse :
      sourceAcquisitionPaysTreatmentReview ≡ false

    controllerCreatesCurrentLawConclusion : Bool
    controllerCreatesCurrentLawConclusionIsFalse :
      controllerCreatesCurrentLawConclusion ≡ false

    controllerCreatesLegalAuthority : Bool
    controllerCreatesLegalAuthorityIsFalse :
      controllerCreatesLegalAuthority ≡ false

canonicalAustralianContractsLandscapeControllerBoundary :
  AustralianContractsLandscapeControllerBoundary
canonicalAustralianContractsLandscapeControllerBoundary =
  australianContractsLandscapeControllerBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
