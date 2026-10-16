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
    "target neural isotope-resolved donor-recipient BH4/BH2 transfer plus multi-branch allocation experiment"
    "very high: carrier existence, cellular uptake, catecholaminergic release, functional coculture crosstalk, ENT/OAT pterin transport and one quantitative epithelial transcellular BH4 edge are already paid; the missing scientific edge is target-relevant donor-derived molecular transfer joined to branch/redox mediation"
    "not an attribution target; scientific debt closes only if donor-derived BH4/BH2 transfer rate/direction is measured in the same target-relevant system as BH4/BH2 redox state and multi-branch outputs"
    "primary interventional experiment using stable-isotope or otherwise donor-traceable pterin/BH4, calibrated donor release and recipient intracellular BH4/BH2, plus NAD(P)H/NOS coupling and PAH/TH/TPH/NOS/AGMO branch readouts resolved by route, compartment, cell type, region and time"
    "high experimental cost; transporter identity should be measured/manipulated as a context variable rather than assuming either universal passive diffusion or one universal dedicated carrier"
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
    "Pareto frontier preserves evidentiary impact, provenance closure, primary authority and acquisition cost as distinct dimensions. Carrier/transport testing removes the false binary 'specific carrier versus passive diffusion': mechanism is context-dependent, and a non-neural transcellular BH4 rate is already quantified. The remaining max-value acquisition is target-neural donor-derived molecular transfer joined to route/compartment/redox-resolved multi-branch causal mediation; selection remains a work queue, not a truth or plagiarism ranking."
