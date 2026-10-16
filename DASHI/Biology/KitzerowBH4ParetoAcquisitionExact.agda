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
stanfordContactArtifact = acquisitionTarget
  "Stanford 2023 direct-contact artifact"
  "high: resolves exposure status for a major circuit-level comparison"
  "high: distinguishes originator report from inspected contact provenance"
  "primary correspondence / timestamped institutional artifact"
  "unknown; acquire from public archive or originator-provided artifact with provenance"
  Discovery.residualObservation false refl

brazilCorrespondenceArtifact : AcquisitionTarget
brazilCorrespondenceArtifact = acquisitionTarget
  "Brazil review journal/author correspondence"
  "high: resolves what was communicated, when, and by whom"
  "high: separates chronology/contact from derivation allegation"
  "primary correspondence / journal response"
  "unknown" Discovery.residualObservation false refl

iaccExposureArtifact : AcquisitionTarget
iaccExposureArtifact = acquisitionTarget
  "MedMaps/IACC exposure-chain artifact"
  "medium-high: resolves claimed institutional awareness"
  "high: contact and role chronology"
  "primary email, meeting record or institutional acknowledgement"
  "unknown" Discovery.residualObservation false refl

sameObjectBH4Experiment : AcquisitionTarget
sameObjectBH4Experiment =
  acquisitionTarget
    "target neural donor-labelled BH4/BH2 transfer with simultaneous multi-branch mediation"
    "very high: carrier existence, cellular uptake, release, functional coculture, context-specific transporter mechanisms, epithelial quantitative transport, route-specific extracellular effects, and separate in-vivo TH/TPH activation are already paid; the remaining discriminating edge is donor-resolved transfer causally joined to simultaneous branch responses"
    "not an attribution target; scientific debt closes only if donor-derived BH4/BH2 rate/direction and branch mediation are measured in the same target-relevant system"
    "primary interventional experiment using stable-isotope or otherwise donor-traceable BH4/pterin with donor release, recipient BH4/BH2, NAD(P)H/NOS redox coupling, and simultaneous TH/TPH/NOS/AGMO branch activity/flux plus enzyme/transporter state resolved by compartment/cell/region/time"
    "high experimental cost; historical route/state results remove the need to rediscover that total tissue BH4 and extracellular BH4 are insufficient descriptors"
    Discovery.experimentalDesign false refl

manuscriptHistoryTargets : AcquisitionTarget
manuscriptHistoryTargets = acquisitionTarget
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
    historicalDirectDiscriminatorChangesTargetDefinitionIsTrue : historicalDirectDiscriminatorChangesTargetDefinition ≡ true
    historicalDirectDiscriminatorClosesWholeTarget : Bool
    historicalDirectDiscriminatorClosesWholeTargetIsFalse : historicalDirectDiscriminatorClosesWholeTarget ≡ false
    reading : String

open ParetoAcquisitionFrontier public

canonicalKitzerowAcquisitionFrontier : ParetoAcquisitionFrontier
canonicalKitzerowAcquisitionFrontier =
  paretoAcquisitionFrontier
    (stanfordContactArtifact ∷ brazilCorrespondenceArtifact ∷ iaccExposureArtifact ∷ sameObjectBH4Experiment ∷ manuscriptHistoryTargets ∷ [])
    false refl false refl false refl true refl false refl
    "The scientific target is no longer generic BH4 transport, tissue uptake, TH/TPH responsiveness or extracellular neuromodulation. Those coordinates are partially/directly paid. The max-value residual is one donor-resolved target-neural experiment coupling molecular BH4/BH2 transfer to simultaneous branch/redox mediation while retaining route, transporter, compartment, cell/region and state history. Selection remains a work queue, not a truth or priority ranking."
