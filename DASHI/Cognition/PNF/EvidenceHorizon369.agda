module DASHI.Cognition.PNF.EvidenceHorizon369 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)

import DASHI.Biology.SSP369JResolutionBifiltrationExact as Existing
import DASHI.Core.RelationalHorizon369 as Generic
import DASHI.Foundations.StratifiedResolutionTowerExact as Resolution
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalBranchInterference as Interference
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity

------------------------------------------------------------------------
-- PNF specialisation of the canonical cumulative 3/6/9 horizon.
--
--   H3 : local structural evidence
--   H6 : H3 + discourse/temporal evidence
--   H9 : H6 + external/authority evidence
--
-- Candidate cardinality is unrestricted. Each coordinate retains exact signed
-- evidence; its coarse reinforcing/independent/interfering phase is derived by
-- the existing RelationalBranchInterference classifier.
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
  Generic.Horizon3 (EvidenceCoordinate Candidate localStructuralEvidence)

H6Evidence : Set → Set
H6Evidence Candidate =
  Generic.Horizon6
    (EvidenceCoordinate Candidate localStructuralEvidence)
    (EvidenceCoordinate Candidate discourseTemporalEvidence)

H9Evidence : Set → Set
H9Evidence Candidate =
  Generic.Horizon9
    (EvidenceCoordinate Candidate localStructuralEvidence)
    (EvidenceCoordinate Candidate discourseTemporalEvidence)
    (EvidenceCoordinate Candidate externalAuthorityEvidence)

------------------------------------------------------------------------
-- Compatibility constructors/accessors for the pre-consolidation PNF names.
------------------------------------------------------------------------

h6Evidence :
  ∀ {Candidate} →
  H3Evidence Candidate →
  Existing.Triple (EvidenceCoordinate Candidate discourseTemporalEvidence) →
  H6Evidence Candidate
h6Evidence = Generic.horizon6

localStructural : ∀ {Candidate} → H6Evidence Candidate → H3Evidence Candidate
localStructural = Generic.first3

discourseTemporal :
  ∀ {Candidate} →
  H6Evidence Candidate →
  Existing.Triple (EvidenceCoordinate Candidate discourseTemporalEvidence)
discourseTemporal = Generic.second3

h9Evidence :
  ∀ {Candidate} →
  H6Evidence Candidate →
  Existing.Triple (EvidenceCoordinate Candidate externalAuthorityEvidence) →
  H9Evidence Candidate
h9Evidence = Generic.horizon9

firstSix : ∀ {Candidate} → H9Evidence Candidate → H6Evidence Candidate
firstSix = Generic.first6

externalAuthority :
  ∀ {Candidate} →
  H9Evidence Candidate →
  Existing.Triple (EvidenceCoordinate Candidate externalAuthorityEvidence)
externalAuthority = Generic.third3

project6to3 : ∀ {Candidate} → H6Evidence Candidate → H3Evidence Candidate
project6to3 = Generic.project6to3

project9to6 : ∀ {Candidate} → H9Evidence Candidate → H6Evidence Candidate
project9to6 = Generic.project9to6

------------------------------------------------------------------------
-- Generic resolution × relational-horizon bifiltration.
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
  Existing.mapTriple
    (mapEvidenceCandidate (Resolution.project tower))

coarsenH6 :
  ∀ {tower r} →
  H6AtResolution tower (suc r) →
  H6AtResolution tower r
coarsenH6 {tower} x =
  h6Evidence
    (coarsenH3 {tower = tower} (localStructural x))
    (Existing.mapTriple
      (mapEvidenceCandidate (Resolution.project tower))
      (discourseTemporal x))

coarsenH9 :
  ∀ {tower r} →
  H9AtResolution tower (suc r) →
  H9AtResolution tower r
coarsenH9 {tower} x =
  h9Evidence
    (coarsenH6 {tower = tower} (firstSix x))
    (Existing.mapTriple
      (mapEvidenceCandidate (Resolution.project tower))
      (externalAuthority x))

coarsenThenProject6to3EqualsProjectThenCoarsen :
  ∀ {tower r} (x : H6AtResolution tower (suc r)) →
  project6to3 (coarsenH6 {tower = tower} x)
  ≡ coarsenH3 {tower = tower} (project6to3 x)
coarsenThenProject6to3EqualsProjectThenCoarsen x = refl

coarsenThenProject9to6EqualsProjectThenCoarsen :
  ∀ {tower r} (x : H9AtResolution tower (suc r)) →
  project9to6 (coarsenH9 {tower = tower} x)
  ≡ coarsenH6 {tower = tower} (project9to6 x)
coarsenThenProject9to6EqualsProjectThenCoarsen x = refl

------------------------------------------------------------------------
-- Horizon omission is not refutation.
------------------------------------------------------------------------

data HorizonOmissionAuthority : Set where
  horizonProjectionOnly : HorizonOmissionAuthority

data HorizonOmissionRefutationPermission : HorizonOmissionAuthority → Set where

horizonProjectionCannotRefute :
  HorizonOmissionRefutationPermission horizonProjectionOnly → ⊥
horizonProjectionCannotRefute ()

------------------------------------------------------------------------
-- External/authority evidence at H9 still does not grant world identity.
------------------------------------------------------------------------

data H9WorldPromotionPermission : Set where

h9PresenceAloneCannotPromoteWorldIdentity :
  H9WorldPromotionPermission → ⊥
h9PresenceAloneCannotPromoteWorldIdentity ()

worldIdentityStillUsesExistingAuthority :
  Identity.WorldCanonicalPermission Identity.externalAuthority
worldIdentityStillUsesExistingAuthority =
  Identity.externalAuthorityMayNameWorldEntity

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
    genericRelationalHorizonCoreReused : Bool
    genericRelationalHorizonCoreReusedIsTrue :
      genericRelationalHorizonCoreReused ≡ true

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
    true refl
