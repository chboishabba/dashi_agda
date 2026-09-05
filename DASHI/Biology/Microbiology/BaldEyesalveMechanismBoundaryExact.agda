module DASHI.Biology.Microbiology.BaldEyesalveMechanismBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Microbiology.QuorumSensingContextExact as QS
import DASHI.Chemistry.AlliumOrganosulfurMechanismExact as Allium

------------------------------------------------------------------------
-- BALD'S EYESALVE: PREPARATION x ASSAY x MECHANISM BOUNDARY
--
-- Primary experimental anchors:
--   Harrison et al. 2015, mBio 6:e01129-15.
--     DOI 10.1128/mBio.01129-15 / PMID 26265721
--   Fuchs et al. 2018, PLoS ONE 13:e0208108.
--     DOI 10.1371/journal.pone.0208108 / PMID 30485362
--   Furner-Pardoe et al. 2020, Scientific Reports 10:12687.
--     DOI 10.1038/s41598-020-69273-8
--   Anonye et al. 2020, Scientific Reports 10:17513.
--     DOI 10.1038/s41598-020-74242-2
--
-- Tangential mechanism anchors are intentionally separate and enter only as
-- bounded cross-source bridges, never as proof that the complete historical
-- mixture acts through a single molecular pathway.
------------------------------------------------------------------------

data Ingredient : Set where
  garlic
  onionOrLeek
  wine
  bovineBile
  brassExposure
  : Ingredient

data AssayModel : Set where
  brothCulture
  syntheticWound
  animalWound
  cornealSafetyModel
  : AssayModel

data EndpointKind : Set where
  growthInhibition
  viableCountReduction
  biofilmKilling
  irritation
  cytotoxicity
  quorumReporterChange
  virulenceChange
  : EndpointKind

data EvidenceStatus : Set where
  directlyObserved
  chemicallyIdentified
  supportedByRelatedSource
  mechanisticHypothesis
  openQuestion
  : EvidenceStatus

record Preparation : Set where
  constructor preparation
  field
    garlicPresent : Bool
    onionOrLeekPresent : Bool
    winePresent : Bool
    bovineBilePresent : Bool
    brassExposurePresent : Bool
    incubationDays : Nat
    preparationReference : String

open Preparation public

record AntimicrobialAssayReceipt : Set where
  constructor antimicrobialAssayReceipt
  field
    preparation : Preparation
    pathogenReference : String
    growthState : QS.GrowthState
    model : AssayModel
    endpoint : EndpointKind
    effectReference : String
    sourceReference : String
    status : EvidenceStatus
    scopeBoundary : String

open AntimicrobialAssayReceipt public

canonicalNineDayEyesalve : Preparation
canonicalNineDayEyesalve =
  preparation true true true true true 9
    "reconstructed recipe family used in Harrison 2015 / Fuchs 2018 / Furner-Pardoe 2020; exact batch details remain study-specific"

BE15-planktonic : AntimicrobialAssayReceipt
BE15-planktonic =
  antimicrobialAssayReceipt
    canonicalNineDayEyesalve
    "Staphylococcus aureus"
    QS.planktonic
    brothCulture
    viableCountReduction
    "bactericidal activity observed in the reconstructed preparation"
    "Harrison et al. 2015 DOI 10.1128/mBio.01129-15"
    directlyObserved
    "does not imply the same effect size in biofilm or human infection"

BE15-biofilm : AntimicrobialAssayReceipt
BE15-biofilm =
  antimicrobialAssayReceipt
    canonicalNineDayEyesalve
    "Staphylococcus aureus"
    QS.biofilm
    syntheticWound
    biofilmKilling
    "large viable-count reduction in established biofilm model"
    "Harrison et al. 2015 DOI 10.1128/mBio.01129-15"
    directlyObserved
    "model-specific anti-biofilm result"

BE18-allicin : AntimicrobialAssayReceipt
BE18-allicin =
  antimicrobialAssayReceipt
    canonicalNineDayEyesalve
    "Staphylococcus aureus / Pseudomonas aeruginosa study panel"
    QS.planktonic
    brothCulture
    growthInhibition
    "allicin identified in the active fraction; cysteine depletion removed observable growth inhibition in the tested fraction"
    "Fuchs et al. 2018 DOI 10.1371/journal.pone.0208108"
    chemicallyIdentified
    "principal observed growth-inhibitory compound in this experiment is not equivalent to complete mixture mechanism"

BE20-combinationBiofilm : AntimicrobialAssayReceipt
BE20-combinationBiofilm =
  antimicrobialAssayReceipt
    canonicalNineDayEyesalve
    "multi-species wound-pathogen panel"
    QS.biofilm
    syntheticWound
    biofilmKilling
    "potent anti-biofilm activity required the multi-ingredient formulation in the tested reconstruction"
    "Furner-Pardoe et al. 2020 DOI 10.1038/s41598-020-69273-8"
    directlyObserved
    "activity was context- and organism-dependent; not a universal biofilm-killing theorem"

record TangentialMechanismBridge : Set where
  constructor tangentialMechanismBridge
  field
    sourceCompound : Allium.OrganosulfurCompound
    molecularAction : Allium.MolecularActionKind
    relatedSourceReference : String
    eyesalveComponentConnection : String
    transferStatus : EvidenceStatus
    transferBoundary : String

open TangentialMechanismBridge public

allicinThiolCrossSourceBridge : TangentialMechanismBridge
allicinThiolCrossSourceBridge =
  tangentialMechanismBridge
    Allium.allicin
    Allium.sThioallylation
    "Rabinkov et al. 1998 DOI 10.1016/S0304-4165(97)00104-9; Borlinghaus et al. 2021 PMID 33801955"
    "allicin was chemically identified as the principal observable growth inhibitor in Fuchs et al. 2018"
    supportedByRelatedSource
    "supports a plausible molecular action of an identified eyesalve constituent; does not enumerate all targets or mixture-level routes"

ajoeneQuorumCrossSourceBridge : TangentialMechanismBridge
ajoeneQuorumCrossSourceBridge =
  tangentialMechanismBridge
    Allium.ajoene
    Allium.quorumRegulationInterference
    "Fong et al. 2017 DOI 10.1021/acs.jmedchem.6b01025 and related garlic quorum-sensing literature"
    "garlic-derived organosulfur chemistry supplies a related mechanistic family"
    mechanisticHypothesis
    "does not establish ajoene abundance in the historical preparation or prove quorum sensing mediates its anti-biofilm phenotype"

record BaldEyesalveMechanismBoundary : Set where
  constructor baldEyesalveMechanismBoundary
  field
    historicalRecipeProvesClinicalEfficacy : Bool
    historicalRecipeProvesClinicalEfficacyIsFalse :
      historicalRecipeProvesClinicalEfficacy ≡ false

    planktonicActivityProvesBiofilmActivity : Bool
    planktonicActivityProvesBiofilmActivityIsFalse :
      planktonicActivityProvesBiofilmActivity ≡ false

    principalAllicinFindingProvesCompleteMixtureMechanism : Bool
    principalAllicinFindingProvesCompleteMixtureMechanismIsFalse :
      principalAllicinFindingProvesCompleteMixtureMechanism ≡ false

    antiBiofilmActivityProvesQuorumMediation : Bool
    antiBiofilmActivityProvesQuorumMediationIsFalse :
      antiBiofilmActivityProvesQuorumMediation ≡ false

    relatedGarlicQSSourceTransfersAutomaticallyToEyesalve : Bool
    relatedGarlicQSSourceTransfersAutomaticallyToEyesalveIsFalse :
      relatedGarlicQSSourceTransfersAutomaticallyToEyesalve ≡ false

    preclinicalSafetyProvesHumanSafety : Bool
    preclinicalSafetyProvesHumanSafetyIsFalse :
      preclinicalSafetyProvesHumanSafety ≡ false

    fullMolecularAccountCurrentlyClosed : Bool
    fullMolecularAccountCurrentlyClosedIsFalse :
      fullMolecularAccountCurrentlyClosed ≡ false

    tangentialSourcesCanPopulateBoundedMechanismHypotheses : Bool
    tangentialSourcesCanPopulateBoundedMechanismHypothesesIsTrue :
      tangentialSourcesCanPopulateBoundedMechanismHypotheses ≡ true

canonicalBaldEyesalveMechanismBoundary : BaldEyesalveMechanismBoundary
canonicalBaldEyesalveMechanismBoundary =
  baldEyesalveMechanismBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
