module DASHI.Culture.AmyEskridgePOAMSBoundaryCandidateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.KnowledgeBoundaryCandidateIdentityBidiExact as I

------------------------------------------------------------------------
-- AMY ESKRIDGE / POAMS CANDIDATE SAME-OBJECT WELD
------------------------------------------------------------------------

poamsCandidate : I.CandidateObjectIdentity
poamsCandidate = I.candidate-object-identity
  "Amy Eskridge September 2020 unnamed NASA-review paper"
  "NASA/TM-20205010911, A Study of the Pope-Osborne Angular Momentum Synthesis Theory (POAMS) Including a Mathematical Reformulation and Validation Experiment"
  I.strongCandidate
  ( I.topicOverlap
  ∷ I.authorOrTeamOverlap
  ∷ I.institutionalOverlap
  ∷ I.timelineCompatibility
  ∷ I.laterWitnessLinkage
  ∷ [] )
  "Amy 2020 captured statement; NASA NTRS 20205010911; later Courtney Marchesani report of Aiden Schaeffer interview"
  "The unnamed paper and NASA TM align on advanced-propulsion/spin-coupled-force subject matter, MSFC origin, Eskridge-team lineage, and review/publication chronology. A later report says Falcon Space co-founder Aiden Schaeffer identified Eskridge-Nelson-Schoenfeld (2021) as the NASA paper Amy was transitioning. No primary NASA case number, paper title in Amy's statement, or direct recording of the Schaeffer identification has yet been recovered, so exactIdentity is not promoted."

poamsStrongCandidate : I.StrongObjectCandidate poamsCandidate
poamsStrongCandidate = I.strong-object-candidate refl
  "Strong candidate only: multiple independent compatibility coordinates plus a later witness-linkage report; exact same-object identity remains open."

------------------------------------------------------------------------
-- NASA PROCESS RECEIPT
--
-- NASA STI policy independently establishes that external dissemination of NASA
-- STI is subject to release authorization (NF-1676/DAA or equivalent).  This
-- makes the procedural form of Amy's self-report plausible without implying
-- that her paper was classified, suppressed, denied, or even that POAMS is the
-- same object.
------------------------------------------------------------------------

record NASAReleaseProcessAssessment : Set where
  constructor nasa-release-process-assessment
  field
    externalNASAStiRequiresReleaseAuthorization : Bool
    externalNASAStiRequiresReleaseAuthorizationIsTrue :
      externalNASAStiRequiresReleaseAuthorization ≡ true
    reviewCanCheckRestrictedAccess : Bool
    reviewCanCheckRestrictedAccessIsTrue :
      reviewCanCheckRestrictedAccess ≡ true
    releaseReviewAutomaticallyMeansClassified : Bool
    releaseReviewAutomaticallyMeansClassifiedIsFalse :
      releaseReviewAutomaticallyMeansClassified ≡ false
    releaseReviewAutomaticallyMeansSuppressed : Bool
    releaseReviewAutomaticallyMeansSuppressedIsFalse :
      releaseReviewAutomaticallyMeansSuppressed ≡ false
    nasaProcessReference : String

canonicalNASAReleaseProcessAssessment : NASAReleaseProcessAssessment
canonicalNASAReleaseProcessAssessment = nasa-release-process-assessment
  true refl
  true refl
  false refl
  false refl
  "NASA NPR 2200.2 release-authorization requirements; NASA STI/Public Access guidance"

record CurrentPOAMSCandidateAssessment : Set where
  constructor current-poams-candidate-assessment
  field
    poamsIsStrongCandidate : Bool
    poamsIsStrongCandidateIsTrue : poamsIsStrongCandidate ≡ true
    poamsExactSameObjectEstablished : Bool
    poamsExactSameObjectEstablishedIsFalse :
      poamsExactSameObjectEstablished ≡ false
    poamsPublicReleaseEstablished : Bool
    poamsPublicReleaseEstablishedIsTrue :
      poamsPublicReleaseEstablished ≡ true
    amyUnnamedPaperPublicReleaseEstablished : Bool
    amyUnnamedPaperPublicReleaseEstablishedIsFalse :
      amyUnnamedPaperPublicReleaseEstablished ≡ false
    exactIdentityStillNeedsPrimaryWeld : Bool
    exactIdentityStillNeedsPrimaryWeldIsTrue :
      exactIdentityStillNeedsPrimaryWeld ≡ true

canonicalCurrentPOAMSCandidateAssessment : CurrentPOAMSCandidateAssessment
canonicalCurrentPOAMSCandidateAssessment = current-poams-candidate-assessment
  true refl
  false refl
  true refl
  false refl
  true refl
