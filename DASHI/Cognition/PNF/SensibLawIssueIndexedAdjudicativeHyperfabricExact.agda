module DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer

------------------------------------------------------------------------
-- CROSS-POLLINATED ISSUE FABRIC
--
-- Donor shapes:
--   #705 claim-specific cutsets / first residual
--   #704 residual -> obligation -> discriminator -> evidence probe
--   #697 think/look/test/act move separation
--
-- This does not replace the existing applicability/violation/liability path.
-- It makes that path one projection through a more general issue-indexed DAG.
------------------------------------------------------------------------

record LegalIssue : Set where
  constructor legalIssue
  field
    issueReference : String
    propositionReference : String
    proceedingReference : String
    legalSystemReference : String

open LegalIssue public

data AdjudicativeQuery : Set where
  identifyBurdenQuery
  identifyStandardQuery
  evaluateIssueQuery
  remedyEligibilityQuery
  explainObservedDispositionQuery
  : AdjudicativeQuery

data AdjudicativeCoordinate : Set where
  issuePropositionCoordinate
  burdenAllocationCoordinate
  standardOfProofCoordinate
  resolvedIssueEvidenceCoordinate
  authorityCoordinate
  jurisdictionCoordinate
  temporalValidityCoordinate
  applicabilityCoordinate
  violationCoordinate
  liabilityCoordinate
  harmCoordinate
  protectedInterestCoordinate
  remedySourceCoordinate
  remedyEligibilityCoordinate
  dispositionExplanationCoordinate
  : AdjudicativeCoordinate

record AdjudicativeCutset : Set where
  constructor adjudicativeCutset
  field
    issuePropositionClosed : Bool
    burdenClosed : Bool
    standardClosed : Bool
    evidenceClosed : Bool
    authorityClosed : Bool
    jurisdictionClosed : Bool
    temporalValidityClosed : Bool
    applicabilityClosed : Bool
    violationClosed : Bool
    liabilityClosed : Bool
    harmClosed : Bool
    protectedInterestClosed : Bool
    remedySourceClosed : Bool
    dispositionExplanationClosed : Bool
    cutsetReference : String

open AdjudicativeCutset public

data AdjudicativeResidual : Set where
  issuePropositionResidual
  burdenResidual
  standardResidual
  evidenceResidual
  authorityResidual
  jurisdictionResidual
  temporalValidityResidual
  applicabilityResidual
  violationResidual
  liabilityResidual
  harmResidual
  protectedInterestResidual
  remedySourceResidual
  dispositionExplanationResidual
  adjudicativeClosed
  : AdjudicativeResidual

firstAdjudicativeResidual : AdjudicativeQuery → AdjudicativeCutset → AdjudicativeResidual
firstAdjudicativeResidual identifyBurdenQuery c with issuePropositionClosed c
... | false = issuePropositionResidual
... | true with burdenClosed c
...   | false = burdenResidual
...   | true = adjudicativeClosed
firstAdjudicativeResidual identifyStandardQuery c with issuePropositionClosed c
... | false = issuePropositionResidual
... | true with standardClosed c
...   | false = standardResidual
...   | true = adjudicativeClosed
firstAdjudicativeResidual evaluateIssueQuery c with issuePropositionClosed c
... | false = issuePropositionResidual
... | true with burdenClosed c
...   | false = burdenResidual
...   | true with standardClosed c
...     | false = standardResidual
...     | true with evidenceClosed c
...       | false = evidenceResidual
...       | true with authorityClosed c
...         | false = authorityResidual
...         | true with jurisdictionClosed c
...           | false = jurisdictionResidual
...           | true = adjudicativeClosed
firstAdjudicativeResidual remedyEligibilityQuery c with liabilityClosed c
... | false = liabilityResidual
... | true with remedySourceClosed c
...   | false = remedySourceResidual
...   | true with protectedInterestClosed c
...     | false = protectedInterestResidual
...     | true with harmClosed c
...       | false = harmResidual
...       | true = adjudicativeClosed
firstAdjudicativeResidual explainObservedDispositionQuery c with dispositionExplanationClosed c
... | false = dispositionExplanationResidual
... | true = adjudicativeClosed

------------------------------------------------------------------------
-- Reverse compiler: residual -> obligation -> discriminator -> move kind.
------------------------------------------------------------------------

data LegalProofObligation : Set where
  establishIssueProposition
  allocateBurden
  establishStandard
  establishEvidenceAdequacy
  establishAuthority
  establishJurisdiction
  establishTemporalValidity
  establishApplicability
  establishViolation
  establishLiability
  establishHarm
  establishProtectedInterest
  establishRemedySource
  explainDisposition
  noFurtherObligation
  : LegalProofObligation

data LegalDiscriminator : Set where
  propositionDiscriminator
  burdenRuleDiscriminator
  standardRuleDiscriminator
  evidenceDiscriminator
  authorityDiscriminator
  jurisdictionDiscriminator
  temporalDiscriminator
  applicabilityDiscriminator
  violationDiscriminator
  liabilityDiscriminator
  harmDiscriminator
  protectedInterestDiscriminator
  remedySourceDiscriminator
  dispositionCauseDiscriminator
  noDiscriminator
  : LegalDiscriminator

data EpistemicWorkKind : Set where
  thinkWork lookWork testWork actWork noWork : EpistemicWorkKind

obligationFor : AdjudicativeResidual → LegalProofObligation
obligationFor issuePropositionResidual = establishIssueProposition
obligationFor burdenResidual = allocateBurden
obligationFor standardResidual = establishStandard
obligationFor evidenceResidual = establishEvidenceAdequacy
obligationFor authorityResidual = establishAuthority
obligationFor jurisdictionResidual = establishJurisdiction
obligationFor temporalValidityResidual = establishTemporalValidity
obligationFor applicabilityResidual = establishApplicability
obligationFor violationResidual = establishViolation
obligationFor liabilityResidual = establishLiability
obligationFor harmResidual = establishHarm
obligationFor protectedInterestResidual = establishProtectedInterest
obligationFor remedySourceResidual = establishRemedySource
obligationFor dispositionExplanationResidual = explainDisposition
obligationFor adjudicativeClosed = noFurtherObligation

discriminatorFor : LegalProofObligation → LegalDiscriminator
discriminatorFor establishIssueProposition = propositionDiscriminator
discriminatorFor allocateBurden = burdenRuleDiscriminator
discriminatorFor establishStandard = standardRuleDiscriminator
discriminatorFor establishEvidenceAdequacy = evidenceDiscriminator
discriminatorFor establishAuthority = authorityDiscriminator
discriminatorFor establishJurisdiction = jurisdictionDiscriminator
discriminatorFor establishTemporalValidity = temporalDiscriminator
discriminatorFor establishApplicability = applicabilityDiscriminator
discriminatorFor establishViolation = violationDiscriminator
discriminatorFor establishLiability = liabilityDiscriminator
discriminatorFor establishHarm = harmDiscriminator
discriminatorFor establishProtectedInterest = protectedInterestDiscriminator
discriminatorFor establishRemedySource = remedySourceDiscriminator
discriminatorFor explainDisposition = dispositionCauseDiscriminator
discriminatorFor noFurtherObligation = noDiscriminator

workKindFor : LegalDiscriminator → EpistemicWorkKind
workKindFor propositionDiscriminator = lookWork
workKindFor burdenRuleDiscriminator = lookWork
workKindFor standardRuleDiscriminator = lookWork
workKindFor evidenceDiscriminator = testWork
workKindFor authorityDiscriminator = lookWork
workKindFor jurisdictionDiscriminator = lookWork
workKindFor temporalDiscriminator = lookWork
workKindFor applicabilityDiscriminator = thinkWork
workKindFor violationDiscriminator = thinkWork
workKindFor liabilityDiscriminator = thinkWork
workKindFor harmDiscriminator = testWork
workKindFor protectedInterestDiscriminator = thinkWork
workKindFor remedySourceDiscriminator = lookWork
workKindFor dispositionCauseDiscriminator = testWork
workKindFor noDiscriminator = noWork

record CompiledAdjudicativeSearch : Set where
  constructor compiledAdjudicativeSearch
  field
    consumer : Consumer.ConsumerKind
    issue : LegalIssue
    query : AdjudicativeQuery
    residual : AdjudicativeResidual
    obligation : LegalProofObligation
    discriminator : LegalDiscriminator
    workKind : EpistemicWorkKind
    compilationReference : String

open CompiledAdjudicativeSearch public

compileAdjudicativeSearch :
  Consumer.ConsumerKind → LegalIssue → AdjudicativeQuery → AdjudicativeCutset → CompiledAdjudicativeSearch
compileAdjudicativeSearch consumer issue query cutset =
  let residual = firstAdjudicativeResidual query cutset in
  compiledAdjudicativeSearch consumer issue query residual
    (obligationFor residual)
    (discriminatorFor (obligationFor residual))
    (workKindFor (discriminatorFor (obligationFor residual)))
    "issue/query-specific cutset -> first residual -> proof obligation -> discriminator -> work kind"

------------------------------------------------------------------------
-- Canonical regressions.
------------------------------------------------------------------------

candidateLiabilityButNoRemedySource : AdjudicativeCutset
candidateLiabilityButNoRemedySource =
  adjudicativeCutset true true true true true true true true true true true true false false
    "liability may be available while remedy source remains unresolved"

remedyStopsAtSource :
  firstAdjudicativeResidual remedyEligibilityQuery candidateLiabilityButNoRemedySource
  ≡ remedySourceResidual
remedyStopsAtSource = refl

burdenCanCloseWithoutLiability : AdjudicativeCutset
burdenCanCloseWithoutLiability =
  adjudicativeCutset true true false false false false false false false false false false false false
    "burden allocation can be answered before liability is resolved"

burdenQueryClosesWithoutLiability :
  firstAdjudicativeResidual identifyBurdenQuery burdenCanCloseWithoutLiability
  ≡ adjudicativeClosed
burdenQueryClosesWithoutLiability = refl

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data LiabilityDeterminesBurden : Set where
data LiabilityDeterminesStandard : Set where
data LiabilityDeterminesRemedy : Set where
data ObservedDispositionDeterminesUniqueLegalState : Set where
data LegalConclusionAuthorisesPhysicalAction : Set where

data OneFixedLinearPipelineFitsEveryLegalQuery : Set where

liabilityDoesNotDetermineBurden : LiabilityDeterminesBurden → ⊥
liabilityDoesNotDetermineBurden ()
liabilityDoesNotDetermineStandard : LiabilityDeterminesStandard → ⊥
liabilityDoesNotDetermineStandard ()
liabilityDoesNotDetermineRemedy : LiabilityDeterminesRemedy → ⊥
liabilityDoesNotDetermineRemedy ()
observedDispositionDoesNotIdentifyUniqueLegalState : ObservedDispositionDeterminesUniqueLegalState → ⊥
observedDispositionDoesNotIdentifyUniqueLegalState ()
legalConclusionDoesNotAuthorisePhysicalAction : LegalConclusionAuthorisesPhysicalAction → ⊥
legalConclusionDoesNotAuthorisePhysicalAction ()
oneLinearPipelineDoesNotFitEveryQuery : OneFixedLinearPipelineFitsEveryLegalQuery → ⊥
oneLinearPipelineDoesNotFitEveryQuery ()

record IssueIndexedAdjudicativeBoundary : Set where
  constructor issue-indexed-adjudicative-boundary
  field
    queriesHaveClaimSpecificCutsets : Bool
    firstResidualIsQueryRelative : Bool
    burdenMayCloseBeforeLiability : Bool
    liabilityAutomaticallyFixesStandard : Bool
    liabilityAutomaticallySelectsRemedy : Bool
    observedDispositionUniquelyIdentifiesLegalState : Bool
    workKindSeparatedFromLegalConclusion : Bool

canonicalIssueIndexedAdjudicativeBoundary : IssueIndexedAdjudicativeBoundary
canonicalIssueIndexedAdjudicativeBoundary =
  issue-indexed-adjudicative-boundary true true true false false false true
