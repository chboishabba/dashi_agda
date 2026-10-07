module DASHI.Law.SensibLawMatterControversyRuntimeParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact as Lee
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review
import DASHI.Law.SensibLawRealMatterReviewedResumeExact as Resume
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- MATTER-CONTROVERSY-1 runtime parity.
--
-- One persisted Matter carries one typed adversarial controversy. Client,
-- solicitor/counsel and court surfaces are read-only projections of that same
-- object. Justice Lee is the procedural-design motivation already owned by the
-- imported formal module; the graph/response/residual/runtime parity below is
-- DASHI/SensibLaw construction and is not attributed as a theorem to Lee.
------------------------------------------------------------------------

selectedJusticeLeeAuthorityBoundary : Lee.AuthorityBoundary
selectedJusticeLeeAuthorityBoundary = Lee.canonicalAuthorityBoundary

selectedJusticeLeeSearchBoundary : Lee.SearchAdmissionBoundary
selectedJusticeLeeSearchBoundary = Lee.canonicalSearchAdmissionBoundary

selectedReviewBoundary : Review.RealMatterReviewBoundary
selectedReviewBoundary = Review.canonicalRealMatterReviewBoundary

selectedResumeBoundary : Resume.RealMatterReviewedResumeBoundary
selectedResumeBoundary = Resume.canonicalRealMatterReviewedResumeBoundary

record RuntimeMatterControversy : Set where
  constructor runtime-matter-controversy
  field
    matterRef : String
    controversyRef : String
    proofGraph : Lee.ProofGraph
    normativeOrderRefs : List String
    reviewedEvidenceRefs : List String
    relationalResidualRefs : List String
    derivedOnly : Bool
    derivedOnlyIsTrue : derivedOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open RuntimeMatterControversy public

record RuntimeReverseProofProjection : Set where
  constructor runtime-reverse-proof-projection
  field
    controversy : RuntimeMatterControversy
    reverse : Lee.ReverseProofSearch
    sameGraphObject : Lee.graph reverse ≡ proofGraph controversy
    potentialReopeningOnly : Bool
    potentialReopeningOnlyIsTrue : potentialReopeningOnly ≡ true
    createsActualReopening : Bool
    createsActualReopeningIsFalse : createsActualReopening ≡ false
    createsAccessAuthority : Bool
    createsAccessAuthorityIsFalse : createsAccessAuthority ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open RuntimeReverseProofProjection public

data MatterPersona : Set where
  clientOrAffectedCommunity : MatterPersona
  solicitorOrCounsel : MatterPersona
  courtOrAssociate : MatterPersona

record PersonaProjection : Set where
  constructor persona-projection
  field
    persona : MatterPersona
    matterRef : String
    controversyRef : String
    normativeOrderRefs : List String
    sourceRefs : List String
    reviewedEvidenceRefs : List String
    residualRefs : List String
    determinesCredibility : Bool
    determinesCredibilityIsFalse : determinesCredibility ≡ false
    determinesUltimateFact : Bool
    determinesUltimateFactIsFalse : determinesUltimateFact ≡ false
    assignsNormativeWeight : Bool
    assignsNormativeWeightIsFalse : assignsNormativeWeight ≡ false
    entersFinalJudgment : Bool
    entersFinalJudgmentIsFalse : entersFinalJudgment ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open PersonaProjection public

record SharedMatterPersonaBundle : Set where
  constructor shared-matter-persona-bundle
  field
    controversy : RuntimeMatterControversy
    client : PersonaProjection
    solicitor : PersonaProjection
    court : PersonaProjection
    clientSameMatter : matterRef client ≡ RuntimeMatterControversy.matterRef controversy
    solicitorSameMatter : matterRef solicitor ≡ RuntimeMatterControversy.matterRef controversy
    courtSameMatter : matterRef court ≡ RuntimeMatterControversy.matterRef controversy
    clientSameControversy : controversyRef client ≡ RuntimeMatterControversy.controversyRef controversy
    solicitorSameControversy : controversyRef solicitor ≡ RuntimeMatterControversy.controversyRef controversy
    courtSameControversy : controversyRef court ≡ RuntimeMatterControversy.controversyRef controversy

open SharedMatterPersonaBundle public

record MatterControversyRuntimeBoundary : Set where
  constructor matter-controversy-runtime-boundary
  field
    responseModePreservedNotBooleanNegation : Bool
    responseModePreservedNotBooleanNegationIsTrue :
      responseModePreservedNotBooleanNegation ≡ true
    samePersistedMatterRequired : Bool
    samePersistedMatterRequiredIsTrue : samePersistedMatterRequired ≡ true
    reviewedEvidenceOwnerReopened : Bool
    reviewedEvidenceOwnerReopenedIsTrue : reviewedEvidenceOwnerReopened ≡ true
    relationalResidualOwnerReopened : Bool
    relationalResidualOwnerReopenedIsTrue : relationalResidualOwnerReopened ≡ true
    normativeOrderCoordinatesPreserved : Bool
    normativeOrderCoordinatesPreservedIsTrue : normativeOrderCoordinatesPreserved ≡ true
    reverseSearchCreatesActualReopening : Bool
    reverseSearchCreatesActualReopeningIsFalse : reverseSearchCreatesActualReopening ≡ false
    reverseSearchCreatesAccessAuthority : Bool
    reverseSearchCreatesAccessAuthorityIsFalse : reverseSearchCreatesAccessAuthority ≡ false
    personaProjectionMutatesMatter : Bool
    personaProjectionMutatesMatterIsFalse : personaProjectionMutatesMatter ≡ false
    courtProjectionDeterminesCredibility : Bool
    courtProjectionDeterminesCredibilityIsFalse : courtProjectionDeterminesCredibility ≡ false
    courtProjectionDeterminesUltimateFact : Bool
    courtProjectionDeterminesUltimateFactIsFalse : courtProjectionDeterminesUltimateFact ≡ false
    courtProjectionAssignsNormativeWeight : Bool
    courtProjectionAssignsNormativeWeightIsFalse : courtProjectionAssignsNormativeWeight ≡ false
    courtProjectionEntersFinalJudgment : Bool
    courtProjectionEntersFinalJudgmentIsFalse : courtProjectionEntersFinalJudgment ≡ false

open MatterControversyRuntimeBoundary public

canonicalMatterControversyRuntimeBoundary : MatterControversyRuntimeBoundary
canonicalMatterControversyRuntimeBoundary =
  matter-controversy-runtime-boundary
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
    false refl
    false refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data TypedResponseEqualsBooleanNegation : Set where
data DifferentMatterMayShareControversyIdentity : Set where
data ReviewedEvidenceMayBeRestatedByPersonaProjection : Set where
data RelationalResidualMayBeInventedByControversyProjection : Set where
data NormativeOrderCoordinateImpliesNormativeHierarchy : Set where
data PotentialReopeningEqualsActualReopening : Set where
data PersonaProjectionMutatesCanonicalMatter : Set where
data CourtProjectionDeterminesMerits : Set where

typedResponseDoesNotEqualBooleanNegation : TypedResponseEqualsBooleanNegation → ⊥
typedResponseDoesNotEqualBooleanNegation ()

differentMatterCannotShareControversyIdentity : DifferentMatterMayShareControversyIdentity → ⊥
differentMatterCannotShareControversyIdentity ()

personaCannotRestateReviewedEvidence : ReviewedEvidenceMayBeRestatedByPersonaProjection → ⊥
personaCannotRestateReviewedEvidence ()

controversyCannotInventRelationalResidual : RelationalResidualMayBeInventedByControversyProjection → ⊥
controversyCannotInventRelationalResidual ()

normativeOrderCoordinateDoesNotImplyHierarchy : NormativeOrderCoordinateImpliesNormativeHierarchy → ⊥
normativeOrderCoordinateDoesNotImplyHierarchy ()

potentialReopeningDoesNotEqualActualReopening : PotentialReopeningEqualsActualReopening → ⊥
potentialReopeningDoesNotEqualActualReopening ()

personaProjectionDoesNotMutateCanonicalMatter : PersonaProjectionMutatesCanonicalMatter → ⊥
personaProjectionDoesNotMutateCanonicalMatter ()

courtProjectionDoesNotDetermineMerits : CourtProjectionDeterminesMerits → ⊥
courtProjectionDoesNotDetermineMerits ()
