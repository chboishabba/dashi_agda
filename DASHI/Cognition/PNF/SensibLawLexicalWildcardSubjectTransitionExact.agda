module DASHI.Cognition.PNF.SensibLawLexicalWildcardSubjectTransitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact as Wildcard
import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryPNFWorldManifoldExact as Manifold
import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreClassifierExact as Fibre

------------------------------------------------------------------------
-- Subject topology is orthogonal to discourse/speaker topology.
------------------------------------------------------------------------

data SubjectTransitionKind : Set where
  predicateContinuation : SubjectTransitionKind
  subjectIntroduction : SubjectTransitionKind
  subjectChangeOrAddition : SubjectTransitionKind
  subjectPreservedLeft : SubjectTransitionKind
  noLocalSubjectEvidence : SubjectTransitionKind
  unresolvedSubjectTransition : SubjectTransitionKind

record SubjectTransitionObservation : Set where
  constructor subjectTransitionObservation
  field
    boundaryReference : String
    transitionKind : SubjectTransitionKind
    leftLocalSubjectReference : String
    rightLocalSubjectReference : String
    crossingSubjectReference : String
    parserReceiptReference : String
    candidateOnly : Bool

open SubjectTransitionObservation public

-- A subject crossing can mean that the same clause continues across the
-- proposed boundary: subject on one side, governing predicate on the other.
-- A newly introduced grammatical subject is also not by itself a new speaker.

data SubjectTransitionDeterminesSpeakerCut : Set where
subjectTransitionDoesNotDetermineSpeakerCut : SubjectTransitionDeterminesSpeakerCut → ⊥
subjectTransitionDoesNotDetermineSpeakerCut ()

data SubjectIntroductionDeterminesSpeakerChange : Set where
subjectIntroductionDoesNotDetermineSpeakerChange : SubjectIntroductionDeterminesSpeakerChange → ⊥
subjectIntroductionDoesNotDetermineSpeakerChange ()

data PredicateContinuationPermitsHardSpeakerCut : Set where
predicateContinuationDoesNotPermitHardSpeakerCut : PredicateContinuationPermitsHardSpeakerCut → ⊥
predicateContinuationDoesNotPermitHardSpeakerCut ()

------------------------------------------------------------------------
-- Counterfactual lexical-role realizations.
--
-- These are diagnostic perturbations only. They test whether local parser/PNF
-- topology and Pareto membership are invariant to uncertainty about one token's
-- lexical realization. They do not assert that any replacement is the word's
-- true part of speech, entity identity, spelling, or meaning.
------------------------------------------------------------------------

data LexicalRoleRealization : Set where
  observedSurface : LexicalRoleRealization
  lowerWildcardSurface : LexicalRoleRealization
  upperWildcardSurface : LexicalRoleRealization
  properNounLikeSurface : LexicalRoleRealization
  commonNounLikeSurface : LexicalRoleRealization
  verbLikeSurface : LexicalRoleRealization
  punctuationLikeSurface : LexicalRoleRealization

record LexicalCounterfactualRun : Set where
  constructor lexicalCounterfactualRun
  field
    realization : LexicalRoleRealization
    replacementSurface : String
    parserReceiptReference : String
    pnfReceiptReference : String
    cutReceiptReference : String
    manifoldReceiptReference : String
    graphReceiptReference : String
    paretoFibreReference : String
    pnfTopologyReference : String

open LexicalCounterfactualRun public

record LexicalCounterfactualEnvelopeReceipt : Set where
  constructor lexicalCounterfactualEnvelopeReceipt
  field
    sourceReference : String
    sentenceReference : String
    tokenReference : String
    observedSurfaceReference : String
    runs : List LexicalCounterfactualRun
    mustFibreReference : String
    mayFibreReference : String
    invariantMembershipReference : String
    ambiguityResidualReference : String
    wildcardOwnerReference : String
    candidateOnly : Bool

open LexicalCounterfactualEnvelopeReceipt public

------------------------------------------------------------------------
-- Existing wildcard owner is the mathematical anchor.
--
-- AmbiguityPreservingBoundedWildcardExact owns the MUST/MAY rule: only
-- membership invariant over every admissible realization can be compressed;
-- disagreement remains an explicit ambiguity residual. The runtime
-- intersection/union over bounded lexical-role realizations is a finite
-- diagnostic consumer of that rule, not a replacement formalism.
------------------------------------------------------------------------

wildcardOwnerReference : String
wildcardOwnerReference =
  "DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact:MembershipEnvelope/InvariantTopK/ambiguousResidual"

record LexicalWildcardBoundary : Set where
  constructor lexicalWildcardBoundary
  field
    capitalizationDeterminesEntityIdentity : Bool
    parserPOSDeterminesWorldIdentity : Bool
    oneRealizationDeterminesDiscourseRole : Bool
    invariantAcrossRealizationsMaySupportAdmission : Bool
    disagreementAcrossRealizationsRemainsResidual : Bool
    wildcardSubstitutionCreatesWorldFact : Bool
    subjectTransitionRemainsIndependentOfSpeakerTransition : Bool

canonicalLexicalWildcardBoundary : LexicalWildcardBoundary
canonicalLexicalWildcardBoundary =
  lexicalWildcardBoundary false false false true true false true

------------------------------------------------------------------------
-- ABC regression coordinate.
------------------------------------------------------------------------

milibandCounterfactualRegression : String
milibandCounterfactualRegression =
  "ABC specimen sentence 2: observed lowercase miliband is parser-labelled NOUN/nsubj; perturb the surface across bounded lexical-role realizations and compare PNF topology/Pareto membership. The probe tests stability only and does not establish the person's identity or correct orthography."

milibandBoundaryExpectation : String
milibandBoundaryExpectation =
  "miliband|also should be classified as predicateContinuation whenever a subject-to-governing-predicate relation crosses the boundary; predicateContinuation blocks hard speaker segmentation independently of lexical identity."

manifoldBoundaryAnchor : Manifold.PNFWorldManifoldBoundary
manifoldBoundaryAnchor = Manifold.canonicalPNFWorldManifoldBoundary

fibreBoundaryAnchor : Fibre.FibreClassifierBoundary
fibreBoundaryAnchor = Fibre.canonicalFibreClassifierBoundary
