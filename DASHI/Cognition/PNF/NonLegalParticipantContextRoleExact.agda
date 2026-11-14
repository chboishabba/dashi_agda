{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.NonLegalParticipantContextRoleExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Spacy
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- GENERAL NON-LEGAL PARTICIPANT / CONTEXT ROLE SURFACE
--
-- O. Objective.
-- Add stronger general participant/context roles for parser-derived PNF motifs.
--
-- R. Reuse.
-- Reuse the existing spaCy DependencyShape carrier.
-- Reuse the existing noTypedMeet residual carrier.
--
-- C. Construction.
-- Keep participant, property-context, and modality-context as distinct axes.
--
-- S. Safety.
-- A parser role is a candidate role.
-- A participant role is not a legal role.
-- A nominal modifier does not prove ownership.
-- A modal auxiliary does not determine deontic force.
-- Distinct role coordinates remain pairwise noTypedMeet.
--
-- L. Lane.
-- This module owns only general non-legal participant/context roles.
--
-- P. Postcondition.
-- The target macroscopic eigen-motif has typed actor, property, and modality
-- coordinates with exact parser-shape witnesses.
--
-- G. Governance.
-- No authority, legal status, ownership, or proposition truth is promoted.
--
-- F. Verification.
-- Canonical equalities and pairwise noTypedMeet lemmas reduce by refl.
------------------------------------------------------------------------

data RoleCoordinate : Set where
  participantCoordinate : RoleCoordinate
  propertyContextCoordinate : RoleCoordinate
  modalityContextCoordinate : RoleCoordinate

data NonLegalParticipantRole : Set where
  actorParticipant : NonLegalParticipantRole
  patientParticipant : NonLegalParticipantRole
  themeParticipant : NonLegalParticipantRole
  experiencerParticipant : NonLegalParticipantRole
  recipientParticipant : NonLegalParticipantRole
  beneficiaryParticipant : NonLegalParticipantRole
  instrumentParticipant : NonLegalParticipantRole
  unresolvedParticipant : NonLegalParticipantRole

data NonLegalContextRole : Set where
  propertyContext : NonLegalContextRole
  modalityContext : NonLegalContextRole
  temporalContext : NonLegalContextRole
  qualifierContext : NonLegalContextRole
  relationContext : NonLegalContextRole
  unresolvedContext : NonLegalContextRole

data GeneralRole : Set where
  participantRole : NonLegalParticipantRole → GeneralRole
  contextRole : NonLegalContextRole → GeneralRole

record RoleAssignment : Set where
  constructor role-assignment
  field
    surfaceReference : String
    dependencyShape : Spacy.DependencyShape
    coordinate : RoleCoordinate
    role : GeneralRole
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open RoleAssignment public

candidateRoleForShape : String → Spacy.DependencyShape → RoleAssignment
candidateRoleForShape ref Spacy.nominalSubject =
  role-assignment ref Spacy.nominalSubject participantCoordinate
    (participantRole actorParticipant) true refl
candidateRoleForShape ref Spacy.directObject =
  role-assignment ref Spacy.directObject participantCoordinate
    (participantRole patientParticipant) true refl
candidateRoleForShape ref Spacy.passiveSubject =
  role-assignment ref Spacy.passiveSubject participantCoordinate
    (participantRole themeParticipant) true refl
candidateRoleForShape ref Spacy.adjectivalModifier =
  role-assignment ref Spacy.adjectivalModifier propertyContextCoordinate
    (contextRole qualifierContext) true refl
candidateRoleForShape ref Spacy.nominalModifier =
  role-assignment ref Spacy.nominalModifier propertyContextCoordinate
    (contextRole propertyContext) true refl
candidateRoleForShape ref Spacy.conjunction =
  role-assignment ref Spacy.conjunction propertyContextCoordinate
    (contextRole relationContext) true refl
candidateRoleForShape ref Spacy.negation =
  role-assignment ref Spacy.negation modalityContextCoordinate
    (contextRole qualifierContext) true refl
candidateRoleForShape ref Spacy.modalAuxiliary =
  role-assignment ref Spacy.modalAuxiliary modalityContextCoordinate
    (contextRole modalityContext) true refl
candidateRoleForShape ref Spacy.determiner =
  role-assignment ref Spacy.determiner propertyContextCoordinate
    (contextRole qualifierContext) true refl
candidateRoleForShape ref Spacy.temporalModifier =
  role-assignment ref Spacy.temporalModifier propertyContextCoordinate
    (contextRole temporalContext) true refl
candidateRoleForShape ref Spacy.clausalComplement =
  role-assignment ref Spacy.clausalComplement propertyContextCoordinate
    (contextRole relationContext) true refl
candidateRoleForShape ref Spacy.openClausalComplement =
  role-assignment ref Spacy.openClausalComplement propertyContextCoordinate
    (contextRole relationContext) true refl
candidateRoleForShape ref Spacy.adverbialClause =
  role-assignment ref Spacy.adverbialClause propertyContextCoordinate
    (contextRole relationContext) true refl
candidateRoleForShape ref Spacy.clausalModifier =
  role-assignment ref Spacy.clausalModifier propertyContextCoordinate
    (contextRole relationContext) true refl
candidateRoleForShape ref Spacy.relativeClause =
  role-assignment ref Spacy.relativeClause propertyContextCoordinate
    (contextRole relationContext) true refl
candidateRoleForShape ref Spacy.unresolvedDependency =
  role-assignment ref Spacy.unresolvedDependency propertyContextCoordinate
    (contextRole unresolvedContext) true refl

------------------------------------------------------------------------
-- Pairwise typed independence.
------------------------------------------------------------------------

coordinateComparison :
  RoleCoordinate →
  RoleCoordinate →
  Residual.ResidualLevel
coordinateComparison participantCoordinate participantCoordinate = Residual.partial
coordinateComparison participantCoordinate propertyContextCoordinate = Residual.noTypedMeet
coordinateComparison participantCoordinate modalityContextCoordinate = Residual.noTypedMeet
coordinateComparison propertyContextCoordinate participantCoordinate = Residual.noTypedMeet
coordinateComparison propertyContextCoordinate propertyContextCoordinate = Residual.partial
coordinateComparison propertyContextCoordinate modalityContextCoordinate = Residual.noTypedMeet
coordinateComparison modalityContextCoordinate participantCoordinate = Residual.noTypedMeet
coordinateComparison modalityContextCoordinate propertyContextCoordinate = Residual.noTypedMeet
coordinateComparison modalityContextCoordinate modalityContextCoordinate = Residual.partial

participantPropertyNoTypedMeet :
  coordinateComparison participantCoordinate propertyContextCoordinate
  ≡ Residual.noTypedMeet
participantPropertyNoTypedMeet = refl

participantModalityNoTypedMeet :
  coordinateComparison participantCoordinate modalityContextCoordinate
  ≡ Residual.noTypedMeet
participantModalityNoTypedMeet = refl

propertyModalityNoTypedMeet :
  coordinateComparison propertyContextCoordinate modalityContextCoordinate
  ≡ Residual.noTypedMeet
propertyModalityNoTypedMeet = refl

------------------------------------------------------------------------
-- Target macroscopic eigen-motif.
------------------------------------------------------------------------

record MacroscopicEigenMotif : Set where
  constructor macroscopic-eigen-motif
  field
    actor : RoleAssignment
    property : RoleAssignment
    modality : RoleAssignment

    actorCoordinateIsParticipant :
      coordinate actor ≡ participantCoordinate

    propertyCoordinateIsPropertyContext :
      coordinate property ≡ propertyContextCoordinate

    modalityCoordinateIsModalityContext :
      coordinate modality ≡ modalityContextCoordinate

    actorPropertyIndependent :
      coordinateComparison (coordinate actor) (coordinate property)
      ≡ Residual.noTypedMeet

    actorModalityIndependent :
      coordinateComparison (coordinate actor) (coordinate modality)
      ≡ Residual.noTypedMeet

    propertyModalityIndependent :
      coordinateComparison (coordinate property) (coordinate modality)
      ≡ Residual.noTypedMeet

open MacroscopicEigenMotif public

youActorAssignment : RoleAssignment
youActorAssignment =
  candidateRoleForShape "actor:you" Spacy.nominalSubject

chboishabbaPropertyAssignment : RoleAssignment
chboishabbaPropertyAssignment =
  candidateRoleForShape "property:chboishabba" Spacy.nominalModifier

toModalityAssignment : RoleAssignment
toModalityAssignment =
  candidateRoleForShape "modality:to" Spacy.modalAuxiliary

canonicalMacroscopicEigenMotif : MacroscopicEigenMotif
canonicalMacroscopicEigenMotif =
  macroscopic-eigen-motif
    youActorAssignment
    chboishabbaPropertyAssignment
    toModalityAssignment
    refl
    refl
    refl
    refl
    refl
    refl

actorShapeIsNominalSubject :
  dependencyShape (actor canonicalMacroscopicEigenMotif)
  ≡ Spacy.nominalSubject
actorShapeIsNominalSubject = refl

propertyShapeIsNominalModifier :
  dependencyShape (property canonicalMacroscopicEigenMotif)
  ≡ Spacy.nominalModifier
propertyShapeIsNominalModifier = refl

modalityShapeIsModalAuxiliary :
  dependencyShape (modality canonicalMacroscopicEigenMotif)
  ≡ Spacy.modalAuxiliary
modalityShapeIsModalAuxiliary = refl

------------------------------------------------------------------------
-- Zero-trust semantic boundary.
------------------------------------------------------------------------

record NonLegalParticipantContextBoundary : Set where
  constructor non-legal-participant-context-boundary
  field
    parserParticipantRoleCreatesLegalRole : Bool
    parserParticipantRoleCreatesLegalRoleIsFalse :
      parserParticipantRoleCreatesLegalRole ≡ false

    nominalModifierCreatesOwnership : Bool
    nominalModifierCreatesOwnershipIsFalse :
      nominalModifierCreatesOwnership ≡ false

    modalAuxiliaryCreatesDeonticForce : Bool
    modalAuxiliaryCreatesDeonticForceIsFalse :
      modalAuxiliaryCreatesDeonticForce ≡ false

    participantRoleCreatesAuthority : Bool
    participantRoleCreatesAuthorityIsFalse :
      participantRoleCreatesAuthority ≡ false

    roleCandidateCreatesWorldFact : Bool
    roleCandidateCreatesWorldFactIsFalse :
      roleCandidateCreatesWorldFact ≡ false

    roleCoordinatesArePairwiseIndependent : Bool
    roleCoordinatesArePairwiseIndependentIsTrue :
      roleCoordinatesArePairwiseIndependent ≡ true

canonicalNonLegalParticipantContextBoundary :
  NonLegalParticipantContextBoundary
canonicalNonLegalParticipantContextBoundary =
  non-legal-participant-context-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
