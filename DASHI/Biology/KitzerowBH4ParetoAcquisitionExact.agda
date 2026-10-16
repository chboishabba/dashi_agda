module DASHI.Biology.KitzerowBH4ParetoAcquisitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery

record AcquisitionTarget : Set where
  constructor acquisitionTarget
  field
    label : String
    evidentiaryImpact : String
    provenanceClosure : String
    primaryAuthority : String
    accessCost : String
    discoveryRoute : Discovery.DiscoveryRoute
    createsTruthBySelection : Bool
    createsTruthBySelectionIsFalse : createsTruthBySelection ≡ false

open AcquisitionTarget public

stanfordContactArtifact : AcquisitionTarget
stanfordContactArtifact =
  acquisitionTarget
    "Stanford 2023 direct-contact artifact"
    "high: resolves exposure status for a major circuit-level comparison"
    "high: distinguishes originator report from inspected contact provenance"
    "primary correspondence / timestamped institutional artifact"
    "unknown; acquire from public archive or originator-provided artifact with provenance"
    Discovery.residualObservation
    false refl

brazilCorrespondenceArtifact : AcquisitionTarget
brazilCorrespondenceArtifact =
  acquisitionTarget
    "Brazil review journal/author correspondence"
    "high: resolves what was communicated, when, and by whom"
    "high: separates chronology/contact from derivation allegation"
    "primary correspondence / journal response"
    "unknown"
    Discovery.residualObservation
    false refl

iaccExposureArtifact : AcquisitionTarget
iaccExposureArtifact =
  acquisitionTarget
    "MedMaps/IACC exposure-chain artifact"
    "medium-high: resolves claimed institutional awareness"
    "high: contact and role chronology"
    "primary email, meeting record or institutional acknowledgement"
    "unknown"
    Discovery.residualObservation
    false refl

sameObjectBH4Experiment : AcquisitionTarget
sameObjectBH4Experiment =
  acquisitionTarget
    "target-relevant multi-branch BH4 allocation experiment beyond paid hepatic and neural precedents"
    "very high: directly targets the remaining live central causal edge after Pastor 1996 constrains PAH-iNOS competition and Hyland/Jiang constrain current-pool rescue sufficiency"
    "not an attribution target; closes scientific mechanism debt only if it extends beyond the paid rat-hepatic and mouse neural/developmental contexts"
    "primary interventional experiment with calibrated BH4/BH2 + NAD(P)H + PAH/TH/TPH/NOS/AGMO flux and enzyme-state readouts resolved by compartment/cell type/region/time"
    "high experimental cost; historical direct constraints reduce model/design uncertainty but not the remaining target-relevant acquisition burden"
    Discovery.experimentalDesign
    false refl

manuscriptHistoryTargets : AcquisitionTarget
manuscriptHistoryTargets =
  acquisitionTarget
    "comparison-paper manuscript/preprint histories"
    "high where priority or access timing is disputed"
    "high: pins what existed before/after alleged exposure"
    "publisher history, preprint versions, archived drafts where public"
    "low-medium public acquisition cost"
    Discovery.residualObservation
    false refl

record ParetoAcquisitionFrontier : Set where
  constructor paretoAcquisitionFrontier
  field
    targets : List AcquisitionTarget
    dimensionsScalarized : Bool
    dimensionsScalarizedIsFalse : dimensionsScalarized ≡ false
    frontierRankIsTruthRank : Bool
    frontierRankIsTruthRankIsFalse : frontierRankIsTruthRank ≡ false
    selectionCreatesEvidence : Bool
    selectionCreatesEvidenceIsFalse : selectionCreatesEvidence ≡ false
    historicalDirectDiscriminatorChangesTargetDefinition : Bool
    historicalDirectDiscriminatorChangesTargetDefinitionIsTrue :
      historicalDirectDiscriminatorChangesTargetDefinition ≡ true
    historicalDirectDiscriminatorClosesWholeTarget : Bool
    historicalDirectDiscriminatorClosesWholeTargetIsFalse :
      historicalDirectDiscriminatorClosesWholeTarget ≡ false
    reading : String

open ParetoAcquisitionFrontier public

canonicalKitzerowAcquisitionFrontier : ParetoAcquisitionFrontier
canonicalKitzerowAcquisitionFrontier =
  paretoAcquisitionFrontier
    (stanfordContactArtifact
      ∷ brazilCorrespondenceArtifact
      ∷ iaccExposureArtifact
      ∷ sameObjectBH4Experiment
      ∷ manuscriptHistoryTargets
      ∷ [])
    false refl
    false refl
    false refl
    true refl
    false refl
    "Pareto frontier preserves evidentiary impact, provenance closure, primary authority and acquisition cost as distinct dimensions. Existing hepatic competition and neural rescue/context counterexamples change the scientific target from generic BH4 competition to target-relevant cross-context multi-branch allocation with state-history resolution; selection remains a work queue, not a truth or plagiarism ranking."
