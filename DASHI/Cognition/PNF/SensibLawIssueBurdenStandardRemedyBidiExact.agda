module DASHI.Cognition.PNF.SensibLawIssueBurdenStandardRemedyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue

------------------------------------------------------------------------
-- BURDEN + STANDARD ARE ISSUE-INDEXED, NOT DOWNSTREAM OF LIABILITY.
------------------------------------------------------------------------

record IssueBurdenReceipt (issue : Issue.LegalIssue) : Set where
  constructor issueBurdenReceipt
  field
    burden : Status.BurdenKind
    bearerReference : String
    propositionExact : String
    propositionMatchesIssue : propositionExact ≡ Issue.propositionReference issue
    sourceReferences : List String
    legalSystemExact : String
    legalSystemMatchesIssue : legalSystemExact ≡ Issue.legalSystemReference issue
    resolverReference : String

open IssueBurdenReceipt public

record IssueStandardReceipt (issue : Issue.LegalIssue) : Set where
  constructor issueStandardReceipt
  field
    standard : Status.StandardOfProof
    propositionExact : String
    propositionMatchesIssue : propositionExact ≡ Issue.propositionReference issue
    proceedingExact : String
    proceedingMatchesIssue : proceedingExact ≡ Issue.proceedingReference issue
    sourceReferences : List String
    legalSystemExact : String
    legalSystemMatchesIssue : legalSystemExact ≡ Issue.legalSystemReference issue
    resolverReference : String

open IssueStandardReceipt public

record IssueAdjudicativeFrame (issue : Issue.LegalIssue) : Set where
  constructor issueAdjudicativeFrame
  field
    burdenReceipt : IssueBurdenReceipt issue
    standardReceipt : IssueStandardReceipt issue
    evidenceReference : String
    evidenceAdequacyResolved : Bool
    evidenceAdequacyResolvedIsTrue : evidenceAdequacyResolved ≡ true
    frameReference : String

open IssueAdjudicativeFrame public

------------------------------------------------------------------------
-- REMEDY ELIGIBILITY IS A SEPARATE QUERY-SPECIFIC CONSEQUENCE.
------------------------------------------------------------------------

data RemedyEligibilityStatus : Set where
  remedyEligibilityUnresolved
  remedyEligibilityCandidate
  remedyEligibleAdmitted
  remedyIneligibleAdmitted
  : RemedyEligibilityStatus

data LiabilityRemedyUse : Status.LiabilityStatus → RemedyEligibilityStatus → Set where
  unresolvedLiabilityRemedyUse :
    LiabilityRemedyUse Status.liabilityUnresolved remedyEligibilityUnresolved
  candidateLiabilityRemedyUse :
    LiabilityRemedyUse Status.liabilityCandidate remedyEligibilityCandidate
  admittedLiabilityCandidateRemedyUse :
    LiabilityRemedyUse Status.liabilityAdmitted remedyEligibilityCandidate
  admittedLiabilityEligibleRemedyUse :
    LiabilityRemedyUse Status.liabilityAdmitted remedyEligibleAdmitted
  noLiabilityIneligibleRemedyUse :
    LiabilityRemedyUse Status.noLiabilityAdmitted remedyIneligibleAdmitted

data NonEmpty {A : Set} : List A → Set where
  oneOrMore : ∀ {x xs} → NonEmpty (x ∷ xs)

record RemedyPrerequisiteBundle : Set where
  constructor remedyPrerequisiteBundle
  field
    liabilityReceipt : Legal.LiabilityReceipt
    wrongType : Ontology.WrongType
    sameWrongType :
      wrongType ≡
      Legal.wrongType
        (Legal.applicabilityReceipt
          (Legal.violationReceipt liabilityReceipt))
    remedyReference : Ontology.StableId
    remedyDeclaredForWrongType : remedyReference Legal.∈ Ontology.WrongType.remedyIds wrongType
    protectedInterestReferences : List Ontology.StableId
    protectedInterestsPresent : NonEmpty protectedInterestReferences
    harmReferences : List Ontology.StableId
    harmsPresent : NonEmpty harmReferences
    remedySourceReferences : List String
    remedySourceResolved : Bool
    remedySourceResolvedIsTrue : remedySourceResolved ≡ true
    bundleReference : String

open RemedyPrerequisiteBundle public

record RemedyDecision (prerequisites : RemedyPrerequisiteBundle) : Set where
  constructor remedyDecision
  field
    resultingEligibility : RemedyEligibilityStatus
    liabilityUse :
      LiabilityRemedyUse
        (Legal.resultingLiability (liabilityReceipt prerequisites))
        resultingEligibility
    resolverReference : String

open RemedyDecision public

record RemedyMeetInput : Set where
  constructor remedyMeetInput
  field
    prerequisites : RemedyPrerequisiteBundle
    decision : RemedyDecision prerequisites

open RemedyMeetInput public

compileLegacyRemedyEligibility : RemedyMeetInput → Legal.RemedyEligibilityReceipt
compileLegacyRemedyEligibility input =
  let p = prerequisites input in
  Legal.remedyEligibilityReceipt
    (liabilityReceipt p)
    (remedyReference p)
    (remedyDeclaredForWrongType p)
    (protectedInterestReferences p)
    (harmReferences p)
    (eligibilityBool (resultingEligibility (decision input)))
    (resolverReference (decision input))
  where
  eligibilityBool : RemedyEligibilityStatus → Bool
  eligibilityBool remedyEligibilityUnresolved = false
  eligibilityBool remedyEligibilityCandidate = false
  eligibilityBool remedyEligibleAdmitted = true
  eligibilityBool remedyIneligibleAdmitted = false

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data LiabilityDeterminesIssueBurden : Set where
data LiabilityDeterminesIssueStandard : Set where
data CandidateLiabilityAdmitsRemedyEligibility : Set where
data RemedyDeclaredForWrongTypeAloneMakesEligible : Set where
data EmptyHarmSetMayClosePositiveRemedyEligibility : Set where
data EmptyProtectedInterestSetMayClosePositiveRemedyEligibility : Set where

liabilityDoesNotDetermineIssueBurden : LiabilityDeterminesIssueBurden → ⊥
liabilityDoesNotDetermineIssueBurden ()
liabilityDoesNotDetermineIssueStandard : LiabilityDeterminesIssueStandard → ⊥
liabilityDoesNotDetermineIssueStandard ()
candidateLiabilityDoesNotAdmitRemedy : CandidateLiabilityAdmitsRemedyEligibility → ⊥
candidateLiabilityDoesNotAdmitRemedy ()
remedyDeclarationAloneDoesNotMakeEligible : RemedyDeclaredForWrongTypeAloneMakesEligible → ⊥
remedyDeclarationAloneDoesNotMakeEligible ()
emptyHarmSetDoesNotClosePositiveRemedy : EmptyHarmSetMayClosePositiveRemedyEligibility → ⊥
emptyHarmSetDoesNotClosePositiveRemedy ()
emptyProtectedInterestDoesNotClosePositiveRemedy : EmptyProtectedInterestSetMayClosePositiveRemedyEligibility → ⊥
emptyProtectedInterestDoesNotClosePositiveRemedy ()

record IssueBurdenStandardRemedyBoundary : Set where
  constructor issue-burden-standard-remedy-boundary
  field
    burdenIndexedByIssue : Bool
    standardIndexedByIssueAndProceeding : Bool
    liabilityAutomaticallyFixesBurden : Bool
    liabilityAutomaticallyFixesStandard : Bool
    candidateLiabilityMayAdmitRemedy : Bool
    remedyNeedsDeclaredWrongTypeRemedy : Bool
    remedyNeedsProtectedInterest : Bool
    remedyNeedsHarm : Bool
    remedyNeedsResolvedSource : Bool

canonicalIssueBurdenStandardRemedyBoundary : IssueBurdenStandardRemedyBoundary
canonicalIssueBurdenStandardRemedyBoundary =
  issue-burden-standard-remedy-boundary true true false false false true true true true
