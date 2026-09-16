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
-- A local grammatical transition is not a binary cut/no-cut variable. Keep
-- actor, patient, predicate, clause, coordination, modality and negation as
-- orthogonal observations. A discourse consumer may admit or veto a proposed
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
-- Consumer-specific compatibility matrix.
--
-- The runtime v4 span consumer does not scalarise these coordinates. Speaker
-- cuts are incompatible with actor, patient, predicate-aux or clause
-- continuation. Quote handoffs may cross the content-clause attachment but not
-- actor, patient or predicate-aux continuation. Coordination is retained as a
-- live observation and is not itself a veto.
------------------------------------------------------------------------

record DiscourseRoleCompatibility : Set where
  constructor discourseRoleCompatibility
  field
    speakerVetoActorCrossing : Bool
    speakerVetoPatientCrossing : Bool
    speakerVetoPredicateAuxCrossing : Bool
    speakerVetoClauseCrossing : Bool
    quoteVetoActorCrossing : Bool
    quoteVetoPatientCrossing : Bool
    quoteVetoPredicateAuxCrossing : Bool
    quoteAllowsClauseCrossing : Bool
    coordinationCrossingIsNonfatal : Bool
    uncategorisedCrossingIsNonfatal : Bool

open DiscourseRoleCompatibility public

canonicalDiscourseRoleCompatibility : DiscourseRoleCompatibility
canonicalDiscourseRoleCompatibility =
  discourseRoleCompatibility
    true true true true
    true true true true
    true true

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

data CoordinationCrossingForcesVeto : Set where
coordinationCrossingDoesNotForceVeto : CoordinationCrossingForcesVeto → ⊥
coordinationCrossingDoesNotForceVeto ()

data QuoteClauseCrossingForcesVeto : Set where
quoteClauseCrossingDoesNotForceVeto : QuoteClauseCrossingForcesVeto → ⊥
quoteClauseCrossingDoesNotForceVeto ()

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
    roleCompatibilityIsConsumerSpecific : Bool
    coordinationAloneDoesNotForceVeto : Bool
    quoteClauseAttachmentMayRemainLive : Bool
    roleManifoldCreatesSpeakerIdentity : Bool

canonicalRoleTransitionBoundary : RoleTransitionBoundary
canonicalRoleTransitionBoundary =
  roleTransitionBoundary true true true true true true true true false

manifoldBoundaryAnchor : Manifold.PNFWorldManifoldBoundary
manifoldBoundaryAnchor = Manifold.canonicalPNFWorldManifoldBoundary

lexicalBoundaryAnchor : Lexical.LexicalWildcardBoundary
lexicalBoundaryAnchor = Lexical.canonicalLexicalWildcardBoundary

milibandRegressionReference : String
milibandRegressionReference =
  "Miliband lexical realizations preserve actor-to-predicate continuation/hard-cut rejection; punctuation is a separate structural perturbation and must not be used to falsify lexical invariance."

questionInversionRegressionReference : String
questionInversionRegressionReference =
  "did|the and do|they carry patient plus predicate-aux crossings; the speaker-span consumer must veto them without reclassifying the role manifold as speaker identity."

coordinationRegressionReference : String
coordinationRegressionReference =
  "sentence 45 split 7 carries coordination/other crossings with core actor/patient/clause roles intact; coordination alone must not eliminate the live speaker discourse alternative."
