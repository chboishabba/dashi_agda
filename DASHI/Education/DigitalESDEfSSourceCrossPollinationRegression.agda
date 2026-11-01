module DASHI.Education.DigitalESDEfSSourceCrossPollinationRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDTilburySourceRoleExact as Tilbury
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as Cases
import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as Prior
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid

sourceCandidateCount : Attr.sourceCount
  (Attr.AttributedSourceAtlas.sources Cases.candidateEfSSources) ≡ 16
sourceCandidateCount = refl

firstLocatorPreserved : Cases.CrossPollinationCase.sameLocator Cases.taimurOnuki
  ≡ refl
firstLocatorPreserved = refl

lastLocatorPreserved : Cases.CrossPollinationCase.sameLocator Cases.tilburyWortman2004
  ≡ refl
lastLocatorPreserved = refl

twinCourseCaseStaysCandidate :
  Prior.ReciprocalPedagogicalBridge.promotion
    (Cases.CrossPollinationCase.candidateBridge Cases.taimurOnuki)
  ≡ Prior.candidate
twinCourseCaseStaysCandidate = refl

communityCaseStaysCandidate :
  Prior.ReciprocalPedagogicalBridge.promotion
    (Cases.CrossPollinationCase.candidateBridge Cases.singhCommunity)
  ≡ Prior.candidate
communityCaseStaysCandidate = refl

nonAdmissionRetained :
  Cases.CrossPollinationCase.admittedToFullReview Cases.nilssonDahlstrom ≡ false
nonAdmissionRetained = refl

tilburyReusesExistingSource :
  Cases.CrossPollinationCase.attributedSource Cases.tilburyWortman2004
  ≡ Tilbury.tilburyWortman2004
tilburyReusesExistingSource = refl

ecoCOILCollectiveChallenge :
  Prior.ReciprocalPedagogicalBridge.digitalPrinciple
    (Cases.CrossPollinationCase.candidateBridge Cases.adefilaEcoCOIL)
  ≡ Digital.constitutiveLearnerAgency
ecoCOILCollectiveChallenge = refl

accessibilityTensionUsesExistingBraid :
  Braid.TensionReceipt.relation (Cases.canonicalBraid Cases.jepsenCookeAccessibility)
  ≡ Braid.productiveTension
accessibilityTensionUsesExistingBraid = refl

leadershipChangeUsesExistingBraid :
  Braid.TensionReceipt.relation (Cases.canonicalBraid Cases.ferreiraRyanSystem)
  ≡ Braid.convergence
leadershipChangeUsesExistingBraid = refl

sourceCitationsDoNotImportProof :
  Attr.citationImportsProof Cases.taimurOnukiSource ≡ false
sourceCitationsDoNotImportProof = refl

sourceCitationsDoNotCreateAuthority :
  Attr.citationCreatesAuthority Cases.ryanFerreira2024Source ≡ false
sourceCitationsDoNotCreateAuthority = refl

candidateCaseDoesNotCreateReviewAdmission :
  Cases.CitationCreatesSourceAdmission → ⊥
candidateCaseDoesNotCreateReviewAdmission = Cases.citationDoesNotAdmitSource

crosswalkDoesNotProveEffects :
  Cases.SourceComparisonEstablishesInterventionEffect → ⊥
crosswalkDoesNotProveEffects = Cases.comparisonDoesNotProveEffect

crosswalkDoesNotClaimPublicationNovelty :
  Cases.PreSearchCrosswalkEstablishesPublicationNovelty → ⊥
crosswalkDoesNotClaimPublicationNovelty = Cases.crosswalkDoesNotProveNovelty

reviewCountDoesNotPayOurSearch :
  Cases.EarlierReviewPaysDigitalESDSearchExecution → ⊥
reviewCountDoesNotPayOurSearch = Cases.otherReviewDoesNotPaySearch

universityObserverCannotOverrideCommunity :
  Cases.UniversityVoiceOverridesCommunityAuthority → ⊥
universityObserverCannotOverrideCommunity = Cases.universityDoesNotOverrideCommunity

blackRyanJiCaseStaysCandidate :
  Prior.ReciprocalPedagogicalBridge.promotion
    (Cases.CrossPollinationCase.candidateBridge Cases.blackRyanJiNature)
  ≡ Prior.candidate
blackRyanJiCaseStaysCandidate = refl

unescoIsInstitutionalNotAcademicAuthority :
  Attr.sourceKind Cases.unescoTLSSFSource ≡ Attr.institutionalSource
unescoIsInstitutionalNotAcademicAuthority = refl

leadershipSourceStillUnadmitted :
  Cases.CrossPollinationCase.admittedToFullReview Cases.ferreiraRyanDavisDeepDive
  ≡ false
leadershipSourceStillUnadmitted = refl
