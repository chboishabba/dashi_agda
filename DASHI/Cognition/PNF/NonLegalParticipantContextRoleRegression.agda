{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.NonLegalParticipantContextRoleRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Cognition.PNF.NonLegalParticipantContextRoleExact as Roles
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Spacy
import DASHI.Interop.SensibLawResidualLattice as Residual

actorShapeRegression :
  Roles.dependencyShape
    (Roles.actor Roles.canonicalMacroscopicEigenMotif)
  ≡ Spacy.nominalSubject
actorShapeRegression = refl

propertyShapeRegression :
  Roles.dependencyShape
    (Roles.property Roles.canonicalMacroscopicEigenMotif)
  ≡ Spacy.nominalModifier
propertyShapeRegression = refl

modalityShapeRegression :
  Roles.dependencyShape
    (Roles.modality Roles.canonicalMacroscopicEigenMotif)
  ≡ Spacy.modalAuxiliary
modalityShapeRegression = refl

actorPropertyNoMeetRegression :
  Roles.coordinateComparison
    (Roles.coordinate (Roles.actor Roles.canonicalMacroscopicEigenMotif))
    (Roles.coordinate (Roles.property Roles.canonicalMacroscopicEigenMotif))
  ≡ Residual.noTypedMeet
actorPropertyNoMeetRegression = refl

actorModalityNoMeetRegression :
  Roles.coordinateComparison
    (Roles.coordinate (Roles.actor Roles.canonicalMacroscopicEigenMotif))
    (Roles.coordinate (Roles.modality Roles.canonicalMacroscopicEigenMotif))
  ≡ Residual.noTypedMeet
actorModalityNoMeetRegression = refl

propertyModalityNoMeetRegression :
  Roles.coordinateComparison
    (Roles.coordinate (Roles.property Roles.canonicalMacroscopicEigenMotif))
    (Roles.coordinate (Roles.modality Roles.canonicalMacroscopicEigenMotif))
  ≡ Residual.noTypedMeet
propertyModalityNoMeetRegression = refl

parserRoleDoesNotCreateLegalRole :
  Roles.NonLegalParticipantContextBoundary.parserParticipantRoleCreatesLegalRole
    Roles.canonicalNonLegalParticipantContextBoundary
  ≡ false
parserRoleDoesNotCreateLegalRole = refl

nominalModifierDoesNotCreateOwnership :
  Roles.NonLegalParticipantContextBoundary.nominalModifierCreatesOwnership
    Roles.canonicalNonLegalParticipantContextBoundary
  ≡ false
nominalModifierDoesNotCreateOwnership = refl

modalAuxiliaryDoesNotCreateDeonticForce :
  Roles.NonLegalParticipantContextBoundary.modalAuxiliaryCreatesDeonticForce
    Roles.canonicalNonLegalParticipantContextBoundary
  ≡ false
modalAuxiliaryDoesNotCreateDeonticForce = refl

participantRoleDoesNotCreateAuthority :
  Roles.NonLegalParticipantContextBoundary.participantRoleCreatesAuthority
    Roles.canonicalNonLegalParticipantContextBoundary
  ≡ false
participantRoleDoesNotCreateAuthority = refl

candidateRoleDoesNotCreateWorldFact :
  Roles.NonLegalParticipantContextBoundary.roleCandidateCreatesWorldFact
    Roles.canonicalNonLegalParticipantContextBoundary
  ≡ false
candidateRoleDoesNotCreateWorldFact = refl

pairwiseIndependenceIsExplicit :
  Roles.NonLegalParticipantContextBoundary.roleCoordinatesArePairwiseIndependent
    Roles.canonicalNonLegalParticipantContextBoundary
  ≡ true
pairwiseIndependenceIsExplicit = refl
