module DASHI.Governance.CrenshawJudicialDisagreementExact where

-- Source separation for Payne v Travenol, 673 F.2d 798 (5th Cir. 1982).
-- Majority and Goldberg's partial dissent are not interchangeable owners.
-- The opinion is a source for the court's reported holdings; these finite
-- representation types do not certify an authenticated original artifact.
-- Crenshaw's scholarly analysis is independently attributed and is not
-- judicial authorship or authorship of the DASHI proof.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.CrenshawLegalRepresentationRemedyExact as Payne

data OpinionPart : Set where
  majorityOpinion goldbergPartialDissent : OpinionPart

data PayneIssue : Set where
  classExclusion noticeOfExclusion discriminationFindings
  constructiveSeniority lostEarnings : PayneIssue

data JudicialDisposition : Set where
  exclusionAffirmed exclusionDisputed
  noticeNotRequired noticeDisputed
  findingsAffirmed remedyAdjustmentOrdered : JudicialDisposition

record BoundedJudicialStatement : Set where
  constructor statement
  field
    authorialPart : OpinionPart
    issue : PayneIssue
    statedDisposition : JudicialDisposition
    sourceLocator : String

open BoundedJudicialStatement public

payneMajorityClass : BoundedJudicialStatement
payneMajorityClass =
  statement majorityOpinion classExclusion exclusionAffirmed
    "673 F.2d 798, part II and majority summary point II"

payneDissentClass : BoundedJudicialStatement
payneDissentClass =
  statement goldbergPartialDissent classExclusion exclusionDisputed
    "673 F.2d 798, Goldberg partial dissent, part II"

payneMajorityNotice : BoundedJudicialStatement
payneMajorityNotice =
  statement majorityOpinion noticeOfExclusion noticeNotRequired
    "673 F.2d 798, majority summary point II"

payneDissentNotice : BoundedJudicialStatement
payneDissentNotice =
  statement goldbergPartialDissent noticeOfExclusion noticeDisputed
    "673 F.2d 798, Goldberg partial dissent, part III"

payneMajorityHiring : BoundedJudicialStatement
payneMajorityHiring =
  statement majorityOpinion discriminationFindings findingsAffirmed
    "673 F.2d 798, majority summary point IV"

payneMajoritySeniority : BoundedJudicialStatement
payneMajoritySeniority =
  statement majorityOpinion constructiveSeniority remedyAdjustmentOrdered
    "673 F.2d 798, majority summary point VII"

payneMajorityEarnings : BoundedJudicialStatement
payneMajorityEarnings =
  statement majorityOpinion lostEarnings remedyAdjustmentOrdered
    "673 F.2d 798, majority summary point VII"

-- Finite source-ownership and issue-specificity results.
majorityAndDissentAreDistinct :
  majorityOpinion ≡ goldbergPartialDissent → ⊥
majorityAndDissentAreDistinct ()

exclusionAndRemedyAreDistinctIssues :
  classExclusion ≡ constructiveSeniority → ⊥
exclusionAndRemedyAreDistinctIssues ()

payneMajorityNotGoldberg :
  authorialPart payneMajorityClass ≡
  authorialPart payneDissentClass → ⊥
payneMajorityNotGoldberg = majorityAndDissentAreDistinct

payneDisagreementIsSameIssue :
  issue payneMajorityClass ≡ issue payneDissentClass
payneDisagreementIsSameIssue = refl

payneDissentNotMajorityHolding :
  statedDisposition payneDissentClass ≡
  statedDisposition payneMajorityClass → ⊥
payneDissentNotMajorityHolding ()

-- Collapsing all appellate statements to the same case+issue loses
-- the author's disagreement on the class-exclusion issue.
data OnePayneCase : Set where payne : OnePayneCase

data ClassIssueReading : Set where
  reportedMajority reportedDissent : ClassIssueReading

data ClassIssueStatement : Set where
  majorityClassStatement dissentClassStatement : ClassIssueStatement

caseOnly : ClassIssueStatement → OnePayneCase
caseOnly _ = payne

position : ClassIssueStatement → ClassIssueReading
position majorityClassStatement = reportedMajority
position dissentClassStatement = reportedDissent

caseCitationDoesNotRecoverJudicialPosition :
  INF.NonFactorabilityWitness caseOnly position
caseCitationDoesNotRecoverJudicialPosition =
  INF.nonFactorabilityWitness
    majorityClassStatement dissentClassStatement refl (λ ())

caseCitationCannotSelectJudicialPosition :
  INF.FactorsThrough caseOnly position → ⊥
caseCitationCannotSelectJudicialPosition =
  INF.witnessRulesOutEveryFlatFactorisation
    caseCitationDoesNotRecoverJudicialPosition

anyCaseCitationRechartStillLosesDissent :
  ∀ {R : Set} (rechart : OnePayneCase → R) →
  INF.FactorsThrough (λ s → rechart (caseOnly s)) position → ⊥
anyCaseCitationRechartStillLosesDissent rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart caseCitationDoesNotRecoverJudicialPosition

-- The original remedy/class-scope independence proof is reused;
-- this bridge does not assign the remedies to the excluded subclass.
payneRemedyScopeNonFactorability :
  INF.FactorsThrough Payne.classScope Payne.relief → ⊥
payneRemedyScopeNonFactorability =
  Payne.classScopeCannotDetermineRemedy
