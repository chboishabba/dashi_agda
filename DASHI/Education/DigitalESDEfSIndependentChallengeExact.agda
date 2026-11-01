module DASHI.Education.DigitalESDEfSIndependentChallengeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEfSIndependentDerivationExact as EfS
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital

data ComparisonOutcome : Set where
  candidateConvergence : ComparisonOutcome
  candidateTension : ComparisonOutcome
  unmatchedEfSRequirement : ComparisonOutcome
  openEmpiricalComparison : ComparisonOutcome

data DigitalTarget : Set where
  matched : Digital.TransferablePedagogicalPrinciple → DigitalTarget
  noAssertedMatch : DigitalTarget

record ComparisonReceipt : Set where
  constructor comparison
  field
    independentEfS : EfS.IndependentThemeReceipt
    digitalTarget : DigitalTarget
    outcome : ComparisonOutcome
    interpretation : String
    challengeToDigitalFramework : String
    unresolvedEvidence : String
    authorReviewRequired : Bool
    reviewGate : authorReviewRequired ≡ true
open ComparisonReceipt public

systemsComparison : ComparisonReceipt
systemsComparison = comparison EfS.systemsReceipt
  (matched Digital.contextualCustodianship) candidateConvergence
  "Attention to relational context resembles systems thinking but is not yet a measured systems competence."
  "Assess feedback, boundaries, temporal effects and transfer rather than assuming relational vocabulary suffices."
  "Independent scoring of student systems reasoning and domain transfer."
  true refl

valuesComparison : ComparisonReceipt
valuesComparison = comparison EfS.valuesReceipt
  (matched Digital.feedbackAsRevisableSignal) candidateTension
  "Revisable feedback allows questioning classifications, but value negotiation and justice are not reducible to feedback."
  "Retain independently named normative/value reflection, rather than absorbing it into classification contestability."
  "Learner deliberation, justice-related reasoning, whose values shape evaluation criteria."
  true refl

futuresComparison : ComparisonReceipt
futuresComparison = comparison EfS.futureReceipt
  (matched Digital.iterativeEvidenceReturnAndRecharting) candidateConvergence
  "Iterative revision potentially supports futures literacy but is not identical to imagining alternative futures."
  "Explicitly test anticipatory thinking, alternatives, uncertainty and time horizons."
  "Independent prospective futures competence measurement."
  true refl

collectiveComparison : ComparisonReceipt
collectiveComparison = comparison EfS.collectiveReceipt
  (matched Digital.constitutiveLearnerAgency) candidateTension
  "Individual learner voice and authority need not amount to collaborative or political agency."
  "Open separate collective-action and political-agency obligations."
  "Observed group decision rights, real-world enactment, and collective outcomes."
  true refl

ecologicalComparison : ComparisonReceipt
ecologicalComparison = comparison EfS.ecologicalReceipt noAssertedMatch
  unmatchedEfSRequirement
  "Ecological relationships and more-than-human concerns have no complete same-purpose digital pedagogical counterpart among the seven."
  "Keep ecological orientation as a possible new educational principle rather than treating plural human observers as sufficient."
  "Ecological pedagogy sources, age/context transfer, ecological literacy/action observations."
  true refl

enactmentComparison : ComparisonReceipt
enactmentComparison = comparison EfS.enactmentReceipt
  (matched Digital.situatedRelationalEngagement) candidateTension
  "An engagement mechanism alone cannot establish teachers' EfS understanding or transformative enactment."
  "Add educator preparation/practice and institutional support as independently assessed conditions."
  "Longitudinal teaching-practice evidence outside source population."
  true refl

canonicalChallenges : List ComparisonReceipt
canonicalChallenges =
  systemsComparison ∷ valuesComparison ∷ futuresComparison ∷
  collectiveComparison ∷ ecologicalComparison ∷ enactmentComparison ∷ []

data TwoSidedAlignmentProvesEffect : Set where
data MatchedPrinciplesExhaustEfS : Set where
data UnmatchedThemeIsAutomaticallyNewPrinciple : Set where
twoSidedAlignmentDoesNotProveEffect : TwoSidedAlignmentProvesEffect → ⊥
twoSidedAlignmentDoesNotProveEffect ()
matchedPrinciplesDoNotExhaustEfS : MatchedPrinciplesExhaustEfS → ⊥
matchedPrinciplesDoNotExhaustEfS ()
unmatchedDoesNotAutomaticallyDemandNewPrinciple :
  UnmatchedThemeIsAutomaticallyNewPrinciple → ⊥
unmatchedDoesNotAutomaticallyDemandNewPrinciple ()
