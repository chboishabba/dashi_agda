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
  "high for exposure chronology: authentication could upgrade an originator-reported pre-publication contact to inspected exposure evidence"
  "does not close derivation: authenticated exposure/access remains distinct from documented use"
  "primary correspondence / timestamped institutional artifact"
  "unknown; acquire from public archive or originator-provided artifact with provenance"
  Discovery.residualObservation false refl

brazilCorrespondenceArtifact : AcquisitionTarget
brazilCorrespondenceArtifact = acquisitionTarget
  "Brazil review post-publication journal/author correspondence"
  "medium for derivation, high for later dispute/response chronology: if the contact is post-publication as reported, it cannot establish exposure before the already-published review"
  "authenticates who communicated what and when after publication; derivation requires a separate earlier exposure/manuscript lineage"
  "primary correspondence / journal response"
  "unknown; bounded value means acquire if response chronology matters, not as a substitute for pre-publication derivation evidence"
  Discovery.residualObservation false refl

iaccExposureArtifact : AcquisitionTarget
iaccExposureArtifact = acquisitionTarget
  "MedMaps/IACC exposure-chain artifact"
  "medium-high: can resolve claimed institutional awareness once exact temporal order is authenticated"
  "pays exposure/contact chronology only; direct use and derivation remain separate coordinates"
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
  "comparison-paper pre-publication manuscript/exposure lineage"
  "very high for derivation questions: a versioned manuscript change or authenticated earlier exposure trace can connect an upstream source to a later manifestation where mere chronology/contact cannot"
  "distinguishes quotation/revision/derivation from public availability, structural convergence, downstream republication and post-publication complaint correspondence"
  "versioned preprints/manuscripts/submission history, archived drafts, or authenticated pre-publication source-to-recipient correspondence with exact locators"
  "low-medium where public version history exists; potentially high where primary private artifacts are required"
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
    (stanfordContactArtifact ∷ manuscriptHistoryTargets ∷ iaccExposureArtifact ∷ brazilCorrespondenceArtifact ∷ sameObjectBH4Experiment ∷ [])
    false refl false refl false refl true refl false refl
    "Scientific and attribution acquisition remain separate Pareto axes. The scientific max-value residual is donor-resolved target-neural BH4/BH2 transfer joined to simultaneous branch/redox mediation. For attribution, the hbomberguy/republication/provenance cross-pollination raises pre-publication manuscript/exposure lineage above mere downstream publication count or post-publication correspondence: exposure is not derivation, and later contact cannot establish earlier access. Selection remains a work queue, not a truth, misconduct or legal ranking."
