module DASHI.Cognition.PNF.TemporalRoleWorldAlignment where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity

------------------------------------------------------------------------
-- Local temporal-role fibre.
--
-- A title/role denotes an entity only relative to a supported temporal cell.
-- Multiple entities may occupy the same role in ordered/disjoint cells without
-- contradiction.  This is the formal shape needed for a GWB tranche in which
-- Reagan and Bush can both be locally supported as "President" at different
-- times before any Wikidata/world alignment exists.
------------------------------------------------------------------------

record TemporalCell : Set where
  constructor temporalCell
  field
    startTick endTick : Nat
    startBeforeEnd : startTick ≤ᶜ endTick

open TemporalCell public

record RoleOccupancy : Set where
  constructor roleOccupancy
  field
    occupant : Identity.CanonicalEntity
    role : SymbolId
    occupiedCell : TemporalCell
    occupancyEvidenceId : Nat

open RoleOccupancy public

record OrderedRoleSuccession
    (left right : RoleOccupancy) : Set where
  constructor orderedRoleSuccession
  field
    sameRole : role left ≡ role right
    leftEndsBeforeRightStarts :
      endTick (occupiedCell left) ≤ᶜ startTick (occupiedCell right)

open OrderedRoleSuccession public

record RoleTimeDemand : Set where
  constructor roleTimeDemand
  field
    demandedRole : SymbolId
    demandedCell : TemporalCell

open RoleTimeDemand public

record RoleTimeCandidate
    (demand : RoleTimeDemand)
    (occupancy : RoleOccupancy) : Set where
  constructor roleTimeCandidate
  field
    roleMatches : role occupancy ≡ demandedRole demand
    demandStartsInsideOccupancy :
      startTick (occupiedCell occupancy) ≤ᶜ startTick (demandedCell demand)
    demandEndsInsideOccupancy :
      endTick (demandedCell demand) ≤ᶜ endTick (occupiedCell occupancy)

open RoleTimeCandidate public

------------------------------------------------------------------------
-- Local role resolution and external authority alignment are independent.
------------------------------------------------------------------------

data LocalRoleNeedsWorldAuthorityPermission : Set where

localRoleResolutionDoesNotRequireWorldAuthority :
  LocalRoleNeedsWorldAuthorityPermission → ⊥
localRoleResolutionDoesNotRequireWorldAuthority ()

record ExternalAlignmentCandidate : Set where
  constructor externalAlignmentCandidate
  field
    localEntity : Identity.CanonicalEntity
    externalCandidate : Identity.CanonicalEntity
    externalCandidateHasExternalAuthority :
      Identity.canonicalAuthority externalCandidate ≡ Identity.externalAuthority
    candidateEvidenceCount : Nat

open ExternalAlignmentCandidate public

data ExternalCandidatePromotionPermission : Set where

externalCandidateAloneCannotPromoteWorldIdentity :
  ExternalCandidatePromotionPermission → ⊥
externalCandidateAloneCannotPromoteWorldIdentity ()

------------------------------------------------------------------------
-- A promoted world alignment must travel through the existing proof-relevant
-- identity machinery.  The witness must explicitly be external-alignment
-- evidence and target an external-authority canonical entity.
------------------------------------------------------------------------

record AdmittedWorldAlignment : Set where
  constructor admittedWorldAlignment
  field
    candidate : ExternalAlignmentCandidate
    externalWitness : Identity.AdmittedIdentityWitness
    witnessUsesExternalAlignmentEvidence :
      Identity.witnessEvidenceKind
        (Identity.admittedWitness externalWitness)
      ≡ Identity.externalAlignmentEvidence
    witnessTargetsExternalCandidate :
      Identity.canonicalEntityIdentity
        (Identity.witnessTargetEntity
          (Identity.admittedWitness externalWitness))
      ≡ Identity.canonicalEntityIdentity (externalCandidate candidate)
    witnessHasExternalAuthority :
      Identity.witnessAuthority
        (Identity.admittedWitness externalWitness)
      ≡ Identity.externalAuthority

open AdmittedWorldAlignment public

worldCanonicalPermissionAfterExternalWitness :
  AdmittedWorldAlignment →
  Identity.WorldCanonicalPermission Identity.externalAuthority
worldCanonicalPermissionAfterExternalWitness alignment =
  Identity.externalAuthorityMayNameWorldEntity

record TemporalRoleWorldAlignmentBoundary : Set where
  constructor temporalRoleWorldAlignmentBoundary
  field
    sameRoleAcrossTimeImpliesSameEntity : Bool
    sameRoleAcrossTimeImpliesSameEntityIsFalse :
      sameRoleAcrossTimeImpliesSameEntity ≡ false
    localChronologyRequiresWikidata : Bool
    localChronologyRequiresWikidataIsFalse :
      localChronologyRequiresWikidata ≡ false
    externalCandidateIsWorldIdentityBySimilarity : Bool
    externalCandidateIsWorldIdentityBySimilarityIsFalse :
      externalCandidateIsWorldIdentityBySimilarity ≡ false
    externalWorldPromotionStillProofRelevant : Bool
    externalWorldPromotionStillProofRelevantIsTrue :
      externalWorldPromotionStillProofRelevant ≡ true

open TemporalRoleWorldAlignmentBoundary public

canonicalTemporalRoleWorldAlignmentBoundary : TemporalRoleWorldAlignmentBoundary
canonicalTemporalRoleWorldAlignmentBoundary =
  temporalRoleWorldAlignmentBoundary
    false refl
    false refl
    false refl
    true refl
