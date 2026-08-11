module DASHI.Cognition.PNF.EvidenceHorizon369 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)

import DASHI.Biology.SSP369JResolutionBifiltrationExact as Horizon
import DASHI.Foundations.StratifiedResolutionTowerExact as Resolution
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalBranchInterference as Interference
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
--
-- The ternary direction is also not primitive.  Each coordinate retains a fine
-- signed interaction value and the existing exact classification witness that
-- coarsens it to reinforcing / independent / interfering.  A richer continuous
-- application may refine the fine phase carrier further, but the coarse sign
-- must still be derived rather than independently assigned.
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
    fineSignedEvidence : ℤ
    phaseClassification :
      Interference.ClassifiedInteraction fineSignedEvidence

open EvidenceCoordinate public

phaseDirection :
  ∀ {Candidate family} →
  EvidenceCoordinate Candidate family →
  Selection.InteractionDirection
phaseDirection coordinate =
  Interference.interactionDirection (phaseClassification coordinate)

phaseMagnitude :
  ∀ {Candidate family} →
  EvidenceCoordinate Candidate family → Nat
phaseMagnitude coordinate =
  Interference.interactionMagnitude (phaseClassification coordinate)

mapEvidenceCandidate :
  ∀ {A B family} →
  (A → B) →
  EvidenceCoordinate A family →
  EvidenceCoordinate B family
mapEvidenceCandidate f (evidenceCoordinate candidate value classification) =
  evidenceCoordinate (f candidate) value classification

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
-- Generic resolution × relational-horizon bifiltration.
--
-- Unlike the concrete decimal-address witness in SSP369, this bridge accepts
-- any existing ResolutionTower.  Candidate coordinates live at the tower's
-- current resolution.  Coarsening changes only the candidate coordinate and
-- preserves the exact signed evidence/classification receipt.  Forgetting a
-- 3-coordinate relational block commutes definitionally with coarsening.
------------------------------------------------------------------------

H3AtResolution : Resolution.ResolutionTower → Nat → Set
H3AtResolution tower r = H3Evidence (Resolution.Carrier tower r)

H6AtResolution : Resolution.ResolutionTower → Nat → Set
H6AtResolution tower r = H6Evidence (Resolution.Carrier tower r)

H9AtResolution : Resolution.ResolutionTower → Nat → Set
H9AtResolution tower r = H9Evidence (Resolution.Carrier tower r)

coarsenH3 :
  ∀ {tower r} →
  H3AtResolution tower (suc r) →
  H3AtResolution tower r
coarsenH3 {tower} =
  Horizon.mapTriple
    (mapEvidenceCandidate (Resolution.project tower))

coarsenH6 :
  ∀ {tower r} →
  H6AtResolution tower (suc r) →
  H6AtResolution tower r
coarsenH6 {tower} (h6Evidence firstBlock secondBlock) =
  h6Evidence
    (coarsenH3 {tower = tower} firstBlock)
    (Horizon.mapTriple
      (mapEvidenceCandidate (Resolution.project tower))
      secondBlock)

coarsenH9 :
  ∀ {tower r} →
  H9AtResolution tower (suc r) →
  H9AtResolution tower r
coarsenH9 {tower} (h9Evidence firstSixBlock thirdBlock) =
  h9Evidence
    (coarsenH6 {tower = tower} firstSixBlock)
    (Horizon.mapTriple
      (mapEvidenceCandidate (Resolution.project tower))
      thirdBlock)

coarsenThenProject6to3EqualsProjectThenCoarsen :
  ∀ {tower r} (x : H6AtResolution tower (suc r)) →
  project6to3 (coarsenH6 {tower = tower} x)
  ≡ coarsenH3 {tower = tower} (project6to3 x)
coarsenThenProject6to3EqualsProjectThenCoarsen
    (h6Evidence firstBlock secondBlock) = refl

coarsenThenProject9to6EqualsProjectThenCoarsen :
  ∀ {tower r} (x : H9AtResolution tower (suc r)) →
  project9to6 (coarsenH9 {tower = tower} x)
  ≡ coarsenH6 {tower = tower} (project9to6 x)
coarsenThenProject9to6EqualsProjectThenCoarsen
    (h9Evidence firstSixBlock thirdBlock) = refl

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
    coarsePhaseAssignedWithoutFineSignedWitness : Bool
    coarsePhaseAssignedWithoutFineSignedWitnessIsFalse :
      coarsePhaseAssignedWithoutFineSignedWitness ≡ false
    finiteResolutionHorizonSquaresCommute : Bool
    finiteResolutionHorizonSquaresCommuteIsTrue :
      finiteResolutionHorizonSquaresCommute ≡ true
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
    true refl
    false refl
    false refl
