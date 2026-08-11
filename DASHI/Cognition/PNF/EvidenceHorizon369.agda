module DASHI.Cognition.PNF.EvidenceHorizon369 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Biology.SSP369JResolutionBifiltrationExact as Horizon
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity

------------------------------------------------------------------------
-- PNF specialisation of the existing 3/6/9 cumulative-coordinate pattern.
--
-- The existing SSP369 bifiltration establishes the structural reading:
-- H3 = one three-coordinate block, H6 = H3 + a second block, H9 = H6 + a
-- third block, with relational horizon independent of representation
-- resolution.  We reuse its generic Triple and specialise the three blocks:
--
--   H3 : local structural evidence
--   H6 : H3 + discourse/temporal evidence
--   H9 : H6 + external/authority evidence
--
-- 3/6/9 counts evidence-coordinate slots.  It does NOT constrain candidate
-- fibre cardinality; each coordinate may range over an arbitrary Candidate.
------------------------------------------------------------------------

data EvidenceFamily : Set where
  localStructuralEvidence : EvidenceFamily
  discourseTemporalEvidence : EvidenceFamily
  externalAuthorityEvidence : EvidenceFamily

record EvidenceCoordinate
    (Candidate : Set)
    (family : EvidenceFamily) : Set where
  constructor evidenceCoordinate
  field
    candidate : Candidate
    phaseDirection : Selection.InteractionDirection
    phaseMagnitude : Nat

open EvidenceCoordinate public

H3Evidence : Set → Set
H3Evidence Candidate =
  Horizon.Triple (EvidenceCoordinate Candidate localStructuralEvidence)

record H6Evidence (Candidate : Set) : Set where
  constructor h6Evidence
  field
    localStructural : H3Evidence Candidate
    discourseTemporal :
      Horizon.Triple
        (EvidenceCoordinate Candidate discourseTemporalEvidence)

open H6Evidence public

record H9Evidence (Candidate : Set) : Set where
  constructor h9Evidence
  field
    firstSix : H6Evidence Candidate
    externalAuthority :
      Horizon.Triple
        (EvidenceCoordinate Candidate externalAuthorityEvidence)

open H9Evidence public

project6to3 : ∀ {Candidate} → H6Evidence Candidate → H3Evidence Candidate
project6to3 = localStructural

project9to6 : ∀ {Candidate} → H9Evidence Candidate → H6Evidence Candidate
project9to6 = firstSix

------------------------------------------------------------------------
-- The horizon projection forgets evidence coordinates; it does not assert
-- their falsity.  This mirrors the existing 369 depth projection and the PNF
-- coarse/fine rule that omitted detail remains a residual rather than a
-- semantic rejection.
------------------------------------------------------------------------

data HorizonOmissionAuthority : Set where
  horizonProjectionOnly : HorizonOmissionAuthority

data HorizonOmissionRefutationPermission : HorizonOmissionAuthority → Set where

horizonProjectionCannotRefute :
  HorizonOmissionRefutationPermission horizonProjectionOnly → ⊥
horizonProjectionCannotRefute ()

------------------------------------------------------------------------
-- External/authority evidence is present at H9 but still does not itself grant
-- world-canonical identity.  World promotion continues to require the existing
-- ProofRelevantIdentityFibres external-authority permission/witness path.
------------------------------------------------------------------------

data H9WorldPromotionPermission : Set where

h9PresenceAloneCannotPromoteWorldIdentity :
  H9WorldPromotionPermission → ⊥
h9PresenceAloneCannotPromoteWorldIdentity ()

worldIdentityStillUsesExistingAuthority :
  Identity.WorldCanonicalPermission Identity.externalAuthority
worldIdentityStillUsesExistingAuthority =
  Identity.externalAuthorityMayNameWorldEntity

------------------------------------------------------------------------
-- Relational horizon and representation resolution are explicitly independent.
-- This is a PNF claim boundary, reusing the interpretation already proved by
-- SSP369JResolutionBifiltrationExact rather than constructing another
-- resolution tower.
------------------------------------------------------------------------

record EvidenceHorizon369Boundary : Set where
  constructor evidenceHorizon369Boundary
  field
    threeSixNineCountsCandidates : Bool
    threeSixNineCountsCandidatesIsFalse :
      threeSixNineCountsCandidates ≡ false
    relationalHorizonEqualsResolutionDepth : Bool
    relationalHorizonEqualsResolutionDepthIsFalse :
      relationalHorizonEqualsResolutionDepth ≡ false
    h9AutomaticallyPromotesExternalIdentity : Bool
    h9AutomaticallyPromotesExternalIdentityIsFalse :
      h9AutomaticallyPromotesExternalIdentity ≡ false
    omittedHorizonCoordinateIsRefuted : Bool
    omittedHorizonCoordinateIsRefutedIsFalse :
      omittedHorizonCoordinateIsRefuted ≡ false

open EvidenceHorizon369Boundary public

canonicalEvidenceHorizon369Boundary : EvidenceHorizon369Boundary
canonicalEvidenceHorizon369Boundary =
  evidenceHorizon369Boundary
    false refl
    false refl
    false refl
    false refl
