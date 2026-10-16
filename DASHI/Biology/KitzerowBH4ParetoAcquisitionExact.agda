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
    Discovery.residualObservation false refl

brazilCorrespondenceArtifact : AcquisitionTarget
brazilCorrespondenceArtifact =
  acquisitionTarget
    "Brazil review journal/author correspondence"
    "high: resolves what was communicated, when, and by whom"
    "high: separates chronology/contact from derivation allegation"
    "primary correspondence / journal response"
    "unknown" Discovery.residualObservation false refl

iaccExposureArtifact : AcquisitionTarget
iaccExposureArtifact =
  acquisitionTarget
    "MedMaps/IACC exposure-chain artifact"
    "medium-high: resolves claimed institutional awareness"
    "high: contact and role chronology"
    "primary email, meeting record or institutional acknowledgement"
    "unknown" Discovery.residualObservation false refl

sameObjectBH4Experiment : AcquisitionTarget
sameObjectBH4Experiment =
  acquisitionTarget
    "target-relevant transfer/route-resolved multi-branch BH4 allocation experiment beyond paid hepatic, neural and redox/spatial precedents"
    "very high: targets the remaining central edge after hepatic competition, neural rescue/state-history, NOS-bound redox regeneration, cellular localization, direct BH4 uptake, functional catecholaminergic-to-nNOS coculture crosstalk and intracellular/extracellular route effects have already narrowed the model"
    "not an attribution target; scientific debt closes only if the experiment extends beyond uptake/coculture function to quantitative donor-to-recipient transfer plus simultaneous target-relevant multi-branch mediation"
    "primary interventional experiment with calibrated BH4/BH2 + NAD(P)H + NOS-bound BH4 redox/coupling + PAH/TH/TPH/NOS/AGMO flux, enzyme-state readouts, and preferably isotope-resolved donor-to-recipient BH4 transfer by route, compartment, cell type, region and time"
    "high experimental cost; historical evidence removes scalar/well-mixed and generic-uptake uncertainty but not transfer-flux or whole-network causal debt"
    Discovery.experimentalDesign false refl

manuscriptHistoryTargets : AcquisitionTarget
manuscriptHistoryTargets =
  acquisitionTarget
    "comparison-paper manuscript/preprint histories"
    "high where priority or access timing is disputed"
    "high: pins what existed before/after alleged exposure"
    "publisher history, preprint versions, archived drafts where public"
    "low-medium public acquisition cost"
    Discovery.residualObservation false refl

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
    (stanfordContactArtifact ∷ brazilCorrespondenceArtifact ∷ iaccExposureArtifact ∷ sameObjectBH4Experiment ∷ manuscriptHistoryTargets ∷ [])
    false refl false refl false refl true refl false refl
    "Pareto frontier preserves evidentiary impact, provenance closure, primary authority and acquisition cost as distinct dimensions. Existing hepatic, neural, NOS-redox, localization, uptake/coculture and route-specific experiments move the target from generic BH4 competition to quantitative donor-recipient transfer plus route/compartment-resolved multi-branch causal allocation with state-history and redox resolution; selection remains a work queue, not a truth or plagiarism ranking."
