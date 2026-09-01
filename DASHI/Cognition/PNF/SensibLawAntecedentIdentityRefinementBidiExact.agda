module DASHI.Cognition.PNF.SensibLawAntecedentIdentityRefinementBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution

------------------------------------------------------------------------
-- BIDI CAMPAIGN 3: antecedent/coreference and identity refinement.
--
-- Candidate-set narrowing and identity closure are distinct transitions.  The
-- same SemanticSubject is carried through both lanes; narrowing an antecedent
-- fibre does not mutate identity status by construction.
------------------------------------------------------------------------

record BindingCandidateSnapshot : Set where
  constructor bindingCandidateSnapshot
  field
    candidateSetReference : String
    members : List String
    accessibility : List Constitution.AccessibilityPath
    evidenceReferences : List String

open BindingCandidateSnapshot public

data RefinementDisposition : Set where
  retainedAmbiguity narrowedAmbiguity uniqueCandidate noCandidate
  : RefinementDisposition

record AntecedentRefinementReceipt
    (subject : Status.SemanticSubject) : Set where
  constructor antecedentRefinementReceipt
  field
    before : BindingCandidateSnapshot
    after : BindingCandidateSnapshot
    disposition : RefinementDisposition
    resultingAntecedentStatus : Status.AntecedentStatus
    identityBefore : Status.IdentityStatus
    identityAfter : Status.IdentityStatus
    identityUnchanged : identityBefore ≡ identityAfter
    resolverReference : String
    policyReference : String

open AntecedentRefinementReceipt public

candidateNarrowingWithoutIdentityClosure :
  (subject : Status.SemanticSubject) →
  BindingCandidateSnapshot → BindingCandidateSnapshot →
  String → String → AntecedentRefinementReceipt subject
candidateNarrowingWithoutIdentityClosure subject before after resolver policy =
  antecedentRefinementReceipt
    before
    after
    narrowedAmbiguity
    Status.antecedentNarrowed
    (Status.identityStatus subject)
    (Status.identityStatus subject)
    refl
    resolver
    policy

record IdentityClosureReceipt
    (subject : Status.SemanticSubject) : Set where
  constructor identityClosureReceipt
  field
    sourceCandidateSet : BindingCandidateSnapshot
    resultingIdentity : Status.IdentityStatus
    identityEvidenceReferences : List String
    resolverReference : String
    policyReference : String
    governedAuthorityReference : String

open IdentityClosureReceipt public

------------------------------------------------------------------------
-- BIDI direction: a resolved identity may inform future antecedent refinement,
-- but it does not retroactively replace the candidate-set history.
------------------------------------------------------------------------

record IdentityInformedAntecedentReceipt
    (subject : Status.SemanticSubject) : Set where
  constructor identityInformedAntecedentReceipt
  field
    identityReceipt : IdentityClosureReceipt subject
    priorAntecedentReceipt : AntecedentRefinementReceipt subject
    resultingSnapshot : BindingCandidateSnapshot
    resultingAntecedent : Status.AntecedentStatus
    priorCandidateSetRetainedAsProvenance : String

open IdentityInformedAntecedentReceipt public

------------------------------------------------------------------------
-- Hard no-go laws.
------------------------------------------------------------------------

data UniqueAntecedentAutomaticallyClosesIdentity : Set where
data EmptyAntecedentSetMeansExpletive : Set where
data IdentityClosureDeletesCandidateHistory : Set where
data AccessibilityPathIsIdentityProof : Set where

uniqueAntecedentDoesNotAutoCloseIdentity :
  UniqueAntecedentAutomaticallyClosesIdentity → ⊥
uniqueAntecedentDoesNotAutoCloseIdentity ()

emptyCandidateSetDoesNotProveExpletive : EmptyAntecedentSetMeansExpletive → ⊥
emptyCandidateSetDoesNotProveExpletive ()

identityClosureDoesNotDeleteHistory : IdentityClosureDeletesCandidateHistory → ⊥
identityClosureDoesNotDeleteHistory ()

accessibilityDoesNotProveIdentity : AccessibilityPathIsIdentityProof → ⊥
accessibilityDoesNotProveIdentity ()
