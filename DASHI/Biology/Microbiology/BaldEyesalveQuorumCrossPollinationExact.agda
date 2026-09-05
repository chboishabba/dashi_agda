module DASHI.Biology.Microbiology.BaldEyesalveQuorumCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Core.ContextIndexedSystem as Context
import DASHI.Biology.Microbiology.QuorumSensingContextExact as QS
import DASHI.Biology.Microbiology.BaldEyesalveMechanismBoundaryExact as Eyesalve
import DASHI.Chemistry.AlliumOrganosulfurMechanismExact as Allium

------------------------------------------------------------------------
-- CROSS-POLLINATION LAYER
--
-- Purpose: reuse the repo-wide context-indexed projection architecture for
-- microbiological mechanism claims while preserving evidence provenance.
-- A phenotype is a projection of hidden molecular state under assay context;
-- coarser observations need not determine finer mechanism state.
------------------------------------------------------------------------

data HiddenMicroState : Set where
  thiolDominantState
  quorumPerturbedState
  mixedOrUnknownState
  : HiddenMicroState

data AssayContext : Set where
  planktonicContext
  biofilmContext
  quorumReporterContext
  : AssayContext

data CoarsePhenotype : Set where
  growthReduced
  biofilmReduced
  reporterReduced
  unresolvedPhenotype
  : CoarsePhenotype

phenotypeProject : AssayContext → HiddenMicroState → CoarsePhenotype
phenotypeProject planktonicContext thiolDominantState = growthReduced
phenotypeProject planktonicContext quorumPerturbedState = growthReduced
phenotypeProject planktonicContext mixedOrUnknownState = unresolvedPhenotype
phenotypeProject biofilmContext thiolDominantState = biofilmReduced
phenotypeProject biofilmContext quorumPerturbedState = biofilmReduced
phenotypeProject biofilmContext mixedOrUnknownState = unresolvedPhenotype
phenotypeProject quorumReporterContext thiolDominantState = unresolvedPhenotype
phenotypeProject quorumReporterContext quorumPerturbedState = reporterReduced
phenotypeProject quorumReporterContext mixedOrUnknownState = unresolvedPhenotype

microbiologyContextProjection : Context.ContextIndexedProjection
microbiologyContextProjection = record
  { Hidden = HiddenMicroState
  ; Context = AssayContext
  ; Observable = CoarsePhenotype
  ; project = phenotypeProject
  }

-- Concrete finite ambiguity witness: one coarse planktonic phenotype is
-- compatible with two mechanistically distinct hidden states.
samePlanktonicPhenotypeWitness :
  phenotypeProject planktonicContext thiolDominantState ≡
  phenotypeProject planktonicContext quorumPerturbedState
samePlanktonicPhenotypeWitness = refl

record MechanismProjectionBoundary : Set where
  constructor mechanismProjectionBoundary
  field
    samePhenotypeForcesSameHiddenMechanism : Bool
    samePhenotypeForcesSameHiddenMechanismIsFalse :
      samePhenotypeForcesSameHiddenMechanism ≡ false

    relatedSourceMechanismMaySeedHypothesis : Bool
    relatedSourceMechanismMaySeedHypothesisIsTrue :
      relatedSourceMechanismMaySeedHypothesis ≡ true

    relatedSourceMechanismMayCloseTargetMechanismWithoutWeld : Bool
    relatedSourceMechanismMayCloseTargetMechanismWithoutWeldIsFalse :
      relatedSourceMechanismMayCloseTargetMechanismWithoutWeld ≡ false

    assayContextMustRemainIndexed : Bool
    assayContextMustRemainIndexedIsTrue :
      assayContextMustRemainIndexed ≡ true

canonicalMechanismProjectionBoundary : MechanismProjectionBoundary
canonicalMechanismProjectionBoundary =
  mechanismProjectionBoundary
    false refl
    true refl
    false refl
    true refl

------------------------------------------------------------------------
-- Mechanism-candidate atlas: tangential sources are valuable precisely when
-- represented as candidates with explicit transfer obligations.
------------------------------------------------------------------------

data CandidateLane : Set where
  allicinThiolProteome
  cellularRedoxHomeostasis
  enzymeInhibition
  ajoeneGacRsmQuorumLane
  diallylQSRegulation
  biofilmPenetrationOrMatrixInteraction
  preparationChemistryEvolution
  : CandidateLane

record CrossSourceCandidate : Set where
  constructor crossSourceCandidate
  field
    lane : CandidateLane
    sourceReference : String
    targetSystemReference : String
    directTargetEvidence : Bool
    samePreparationEvidence : Bool
    causalMediationEvidence : Bool
    statusReference : String

open CrossSourceCandidate public

allicinProteomeCandidate : CrossSourceCandidate
allicinProteomeCandidate =
  crossSourceCandidate
    allicinThiolProteome
    "Rabinkov 1998; Borlinghaus 2021; bacterial S-thioallylation literature"
    "Bald's eyesalve allicin-containing reconstruction"
    true
    true
    false
    "strong constituent-level mechanism bridge; mixture-level causal sufficiency remains open"

ajoeneQuorumCandidate : CrossSourceCandidate
ajoeneQuorumCandidate =
  crossSourceCandidate
    ajoeneGacRsmQuorumLane
    "Fong et al. 2017 DOI 10.1021/acs.jmedchem.6b01025 and related garlic QS studies"
    "Bald's eyesalve garlic-derived organosulfur fraction"
    true
    false
    false
    "valuable tangential hypothesis; requires chemical-presence and mediation welds in the eyesalve preparation"

preparationEvolutionCandidate : CrossSourceCandidate
preparationEvolutionCandidate =
  crossSourceCandidate
    preparationChemistryEvolution
    "eyesalve preparation studies plus organosulfur stability/chemistry literature"
    "fresh versus matured reconstructed eyesalve"
    false
    true
    false
    "open metabolomic/time-course lane: composition and active-species evolution should be measured directly"

------------------------------------------------------------------------
-- Explicit weld obligations before a related-source mechanism is promoted.
------------------------------------------------------------------------

record MechanismTransferWeld : Set where
  constructor mechanismTransferWeld
  field
    candidate : CrossSourceCandidate
    compoundOrProcessPresentInTargetPreparation : Bool
    molecularActionObservedInTargetSystem : Bool
    phenotypeTracksMolecularAction : Bool
    perturbationOrRescueSupportsMediation : Bool
    sourceAttributionReference : String

open MechanismTransferWeld public

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    sourceSimilarityEqualsMechanismIdentity : Bool
    sourceSimilarityEqualsMechanismIdentityIsFalse :
      sourceSimilarityEqualsMechanismIdentity ≡ false

    compoundPresenceEqualsPhenotypeMediation : Bool
    compoundPresenceEqualsPhenotypeMediationIsFalse :
      compoundPresenceEqualsPhenotypeMediation ≡ false

    quorumReporterShiftEqualsBiofilmCausation : Bool
    quorumReporterShiftEqualsBiofilmCausationIsFalse :
      quorumReporterShiftEqualsBiofilmCausation ≡ false

    multiOmicsCouldRefineCurrentMechanismPartition : Bool
    multiOmicsCouldRefineCurrentMechanismPartitionIsTrue :
      multiOmicsCouldRefineCurrentMechanismPartition ≡ true

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  crossPollinationBoundary false refl false refl false refl true refl
