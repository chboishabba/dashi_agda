module DASHI.Interop.SLRFragmentEvidenceContractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CLAIM-LOCAL FRAGMENT x EVIDENCE CONTRACTION
--
-- Runtime companions:
--   slr_claim_fragment_projection.py          : slr-claim-fragment-projection-v1
--   slr_fragment_evidence_contraction.py      : slr-fragment-evidence-contraction-v1
--
-- A fragment's provenance and a later evidence object's authority are distinct
-- coordinates. Evidence may contract the attribution/source dimension without
-- rewriting the fragment source, paying whole-claim extent, or promoting truth.
------------------------------------------------------------------------

data FragmentMilestoneState : Set where
  runtimeValidated : FragmentMilestoneState
  formalValidated : FragmentMilestoneState
  active : FragmentMilestoneState
  residualOpen : FragmentMilestoneState

record FragmentValidationReceipt : Set where
  constructor fragmentValidationReceipt
  field
    runtimeSchema : String
    fragmentCount : String
    claimFragmentCount : String
    intermediateFragmentCount : String
    relationCount : String
    exactBoundaryFragmentCount : String
    boundedBoundaryFragmentCount : String
    wholeClaimExtentPaid : Bool
    intermediateSpeakerSegmentsRetained : Bool
    semanticPromotion : Bool
    claimTruthPromoted : Bool
    formalCheckReference : String

open FragmentValidationReceipt public

validatedABCFragmentProjection : FragmentValidationReceipt
validatedABCFragmentProjection = fragmentValidationReceipt
  "slr-claim-fragment-projection-v1"
  "5"
  "4"
  "1"
  "4"
  "2"
  "4"
  false
  true
  false
  false
  "SLRClaimFragmentProjectionExact.agda: 146 modules checked, no errors"

record FragmentEvidenceContractionBoundary : Set where
  constructor fragmentEvidenceContractionBoundary
  field
    fragmentProvenanceSeparateFromEvidenceAuthority : Bool
    evidenceMayContractAttributionSourceDimension : Bool
    evidenceMayRewriteFragmentProvenance : Bool
    evidencePaysWholeClaimExtent : Bool
    evidencePromotesClaimTruth : Bool
    contractionAppendOnly : Bool
    candidateOnly : Bool
    runtimeReference : String

open FragmentEvidenceContractionBoundary public

canonicalFragmentEvidenceContractionBoundary : FragmentEvidenceContractionBoundary
canonicalFragmentEvidenceContractionBoundary = fragmentEvidenceContractionBoundary
  true
  true
  false
  false
  false
  true
  true
  "slr-fragment-evidence-contraction-v1"

------------------------------------------------------------------------
-- Current SLR roadmap after fragment validation.
------------------------------------------------------------------------

record FragmentRoadmapState : Set where
  constructor fragmentRoadmapState
  field
    discourseReconstruction : FragmentMilestoneState
    candidateWorldCarrierParity : FragmentMilestoneState
    canonicalClaimProjection : FragmentMilestoneState
    multiHopDiscoursePath : FragmentMilestoneState
    claimLocalFragmentProjection : FragmentMilestoneState
    fragmentEvidenceContraction : FragmentMilestoneState
    wholeClaimExtentCompletion : FragmentMilestoneState
    substantiveWorldEvidenceAdequacy : FragmentMilestoneState

open FragmentRoadmapState public

currentFragmentRoadmap : FragmentRoadmapState
currentFragmentRoadmap = fragmentRoadmapState
  runtimeValidated
  runtimeValidated
  runtimeValidated
  formalValidated
  formalValidated
  active
  residualOpen
  residualOpen

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FragmentProvenanceIsEvidenceAuthority : Set where
data AttributionEvidencePaysWholeClaimExtent : Set where
data AttributionEvidencePaysClaimTruth : Set where
data LocalFragmentIsWholeClaim : Set where
data IntermediateReporterFragmentMayBeDropped : Set where

data EvidenceContractionMayRewritePriorSource : Set where

fragmentProvenanceIsNotEvidenceAuthority : FragmentProvenanceIsEvidenceAuthority → ⊥
fragmentProvenanceIsNotEvidenceAuthority ()

attributionDoesNotPayWholeExtent : AttributionEvidencePaysWholeClaimExtent → ⊥
attributionDoesNotPayWholeExtent ()

attributionDoesNotPayTruth : AttributionEvidencePaysClaimTruth → ⊥
attributionDoesNotPayTruth ()

localFragmentIsNotWholeClaim : LocalFragmentIsWholeClaim → ⊥
localFragmentIsNotWholeClaim ()

intermediateReporterMayNotBeDropped : IntermediateReporterFragmentMayBeDropped → ⊥
intermediateReporterMayNotBeDropped ()

contractionDoesNotRewritePriorSource : EvidenceContractionMayRewritePriorSource → ⊥
contractionDoesNotRewritePriorSource ()
