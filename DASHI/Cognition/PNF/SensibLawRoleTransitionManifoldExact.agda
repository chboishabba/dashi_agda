module DASHI.Cognition.PNF.SensibLawRoleTransitionManifoldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryPNFWorldManifoldExact as Manifold
import DASHI.Cognition.PNF.SensibLawLexicalWildcardSubjectTransitionExact as Lexical

------------------------------------------------------------------------
-- Role-transition manifold.
--
-- A local grammatical transition is not a binary cut/no-cut variable.  Keep
-- actor, patient, predicate, clause, coordination, modality and negation as
-- orthogonal observations.  A discourse consumer may admit or veto a proposed
-- edge using this fibre without turning any one coordinate into speaker truth.
------------------------------------------------------------------------

data RoleCoordinate : Set where
  actorRole : RoleCoordinate
  patientRole : RoleCoordinate
  predicateRole : RoleCoordinate
  clauseRole : RoleCoordinate
  coordinationRole : RoleCoordinate
  modalityRole : RoleCoordinate
  negationRole : RoleCoordinate

record RoleTransitionObservation : Set where
  constructor roleTransitionObservation
  field
    boundaryReference : String
    crossingRoleReference : String
    leftRoleReference : String
    rightRoleReference : String
    parserReference : String
    candidateOnly : Bool

open RoleTransitionObservation public

record RoleTransitionManifold : Set where
  constructor roleTransitionManifold
  field
    boundaryReference : String
    actor : RoleTransitionObservation
    patient : RoleTransitionObservation
    predicate : RoleTransitionObservation
    clause : RoleTransitionObservation
    coordination : RoleTransitionObservation
    modality : RoleTransitionObservation
    negation : RoleTransitionObservation
    discourseProjectionReference : String
    retainedResidualReference : String

open RoleTransitionManifold public

------------------------------------------------------------------------
-- Perturbation class separation.
------------------------------------------------------------------------

data PerturbationClass : Set where
  lexicalPerturbation : PerturbationClass
  structuralPerturbation : PerturbationClass

record PerturbationEnvelopeReceipt : Set where
  constructor perturbationEnvelopeReceipt
  field
    lexicalProjectionInvariantReference : String
    lexicalRoleInvariantReference : String
    lexicalConsumerInvariantReference : String
    structuralProjectionInvariantReference : String
    structuralRoleInvariantReference : String
    structuralConsumerInvariantReference : String
    ambiguityResidualReference : String

open PerturbationEnvelopeReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RoleChangeDeterminesSpeakerChange : Set where
roleChangeDoesNotDetermineSpeakerChange : RoleChangeDeterminesSpeakerChange → ⊥
roleChangeDoesNotDetermineSpeakerChange ()

data SubjectChangeDeterminesSpeakerChange : Set where
subjectChangeDoesNotDetermineSpeakerChange : SubjectChangeDeterminesSpeakerChange → ⊥
subjectChangeDoesNotDetermineSpeakerChange ()

data PredicateContinuationIsSpeakerCut : Set where
predicateContinuationIsNotSpeakerCut : PredicateContinuationIsSpeakerCut → ⊥
predicateContinuationIsNotSpeakerCut ()

data LexicalAndStructuralPerturbationSameFibre : Set where
lexicalAndStructuralPerturbationAreDistinct : LexicalAndStructuralPerturbationSameFibre → ⊥
lexicalAndStructuralPerturbationAreDistinct ()

data StableProjectionProvesStableRoleManifold : Set where
stableProjectionDoesNotProveStableRoleManifold : StableProjectionProvesStableRoleManifold → ⊥
stableProjectionDoesNotProveStableRoleManifold ()

data StableRoleManifoldProvesSpeakerIdentity : Set where
stableRoleManifoldDoesNotProveSpeakerIdentity : StableRoleManifoldProvesSpeakerIdentity → ⊥
stableRoleManifoldDoesNotProveSpeakerIdentity ()

record RoleTransitionBoundary : Set where
  constructor roleTransitionBoundary
  field
    discourseAndGrammarRemainOrthogonal : Bool
    actorPatientPredicateClauseRetainedSeparately : Bool
    modalityAndNegationRetainedSeparately : Bool
    lexicalAndStructuralPerturbationsSeparated : Bool
    consumerAdmissionMayUseRoleManifold : Bool
    roleManifoldCreatesSpeakerIdentity : Bool

canonicalRoleTransitionBoundary : RoleTransitionBoundary
canonicalRoleTransitionBoundary =
  roleTransitionBoundary true true true true true false

manifoldBoundaryAnchor : Manifold.PNFWorldManifoldBoundary
manifoldBoundaryAnchor = Manifold.canonicalPNFWorldManifoldBoundary

lexicalBoundaryAnchor : Lexical.LexicalWildcardBoundary
lexicalBoundaryAnchor = Lexical.canonicalLexicalWildcardBoundary

milibandRegressionReference : String
milibandRegressionReference =
  "Miliband lexical realizations preserve predicate-continuation/hard-cut rejection; punctuation is a separate structural perturbation and must not be used to falsify lexical invariance."
