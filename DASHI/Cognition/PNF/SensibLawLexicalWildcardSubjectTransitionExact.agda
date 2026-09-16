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
    subjectTransitionReference : String
    pnfTopologyReference : String
    hardCutAdmissionReference : String

open LexicalCounterfactualRun public

-- Projection stability and consumer stability are intentionally separate.
-- A discourse fibre may survive every lexical realization while a richer
-- consumer-visible topology or admission decision changes underneath it.
record CounterfactualConsumerEnvelope : Set where
  constructor counterfactualConsumerEnvelope
  field
    mustFibreReference : String
    mayFibreReference : String
    projectionStable : Bool
    subjectTransitionValuesReference : String
    subjectTransitionStable : Bool
    hardCutMust : Bool
    hardCutMay : Bool
    consumerStable : Bool
    residualReference : String

open CounterfactualConsumerEnvelope public

record LexicalCounterfactualEnvelopeReceipt : Set where
  constructor lexicalCounterfactualEnvelopeReceipt
  field
    sourceReference : String
    sentenceReference : String
    tokenReference : String
    observedSurfaceReference : String
    runs : List LexicalCounterfactualRun
    consumerEnvelope : CounterfactualConsumerEnvelope
    wildcardOwnerReference : String
    candidateOnly : Bool

open LexicalCounterfactualEnvelopeReceipt public

------------------------------------------------------------------------
-- Existing wildcard owner is the mathematical anchor.
------------------------------------------------------------------------

wildcardOwnerReference : String
wildcardOwnerReference =
  "DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact:MembershipEnvelope/InvariantTopK/ambiguousResidual"

-- Stable membership in a coarse projection is not enough to certify a richer
-- consumer.  This is the exact defect exposed by the Miliband perturbation:
-- speaker remains on the Pareto front for every tested lexical realization,
-- while the punctuation-like realization changes the subject topology.

data StableProjectionDeterminesConsumerStability : Set where
stableProjectionDoesNotDetermineConsumerStability : StableProjectionDeterminesConsumerStability → ⊥
stableProjectionDoesNotDetermineConsumerStability ()

data StableSpeakerFibreDeterminesHardCut : Set where
stableSpeakerFibreDoesNotDetermineHardCut : StableSpeakerFibreDeterminesHardCut → ⊥
stableSpeakerFibreDoesNotDetermineHardCut ()

data LexicalReplacementDeterminesTruePOS : Set where
lexicalReplacementDoesNotDetermineTruePOS : LexicalReplacementDeterminesTruePOS → ⊥
lexicalReplacementDoesNotDetermineTruePOS ()

record LexicalWildcardBoundary : Set where
  constructor lexicalWildcardBoundary
  field
    capitalizationDeterminesEntityIdentity : Bool
    parserPOSDeterminesWorldIdentity : Bool
    oneRealizationDeterminesDiscourseRole : Bool
    invariantProjectionDeterminesConsumerAdmission : Bool
    invariantAcrossConsumerSurfaceMaySupportAdmission : Bool
    disagreementAcrossRealizationsRemainsResidual : Bool
    wildcardSubstitutionCreatesWorldFact : Bool
    subjectTransitionRemainsIndependentOfSpeakerTransition : Bool

canonicalLexicalWildcardBoundary : LexicalWildcardBoundary
canonicalLexicalWildcardBoundary =
  lexicalWildcardBoundary false false false false true true false true

------------------------------------------------------------------------
-- ABC regression coordinates.
------------------------------------------------------------------------

milibandCounterfactualRegression : String
milibandCounterfactualRegression =
  "ABC specimen sentence 2: observed lowercase miliband is parser-labelled NOUN/nsubj; bounded lexical replacements keep speaker in the Pareto MUST/MAY envelope, but punctuation-like replacement changes subject topology. Therefore projection stability is strictly weaker than consumer stability."

milibandBoundaryExpectation : String
milibandBoundaryExpectation =
  "miliband|also is predicateContinuation for the observed and word-like realizations because the subject-to-governing-predicate relation crosses the boundary; a punctuation realization may remove that crossing, so hard-cut admission must be computed over the richer consumer envelope rather than inferred from stable speaker Pareto membership."

manifoldBoundaryAnchor : Manifold.PNFWorldManifoldBoundary
manifoldBoundaryAnchor = Manifold.canonicalPNFWorldManifoldBoundary

fibreBoundaryAnchor : Fibre.FibreClassifierBoundary
fibreBoundaryAnchor = Fibre.canonicalFibreClassifierBoundary

wildcardFormalOwnerReference : String
wildcardFormalOwnerReference =
  "DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact"
