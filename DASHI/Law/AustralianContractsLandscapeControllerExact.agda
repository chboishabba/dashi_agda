module DASHI.Law.AustralianContractsLandscapeControllerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe)

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
    false refl
    false refl
