module DASHI.Biology.PMDDHistamineMolecularTargetInstantiationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.NeurochemicalAtomicChemistryBridge as AtomicChem
import DASHI.Biology.NeurochemicalProteinTargetBridge as ProteinTarget
import DASHI.Biology.PMDDHistamineAmplificationExact as PMDD

------------------------------------------------------------------------
-- CONCRETE PMDD / HISTAMINE MOLECULAR-TARGET INSTANTIATION
--
-- This module concretises molecular identity and target-context coordinates
-- needed by the PMDD/histamine amplifier candidate.  Identity and target
-- receipts remain strictly weaker than pharmacological or clinical efficacy.
------------------------------------------------------------------------

data MolecularRole : Set where
  endogenousMediatorRole : MolecularRole
  ovarianSteroidRole : MolecularRole
  neurosteroidRole : MolecularRole
  h1AntagonistProbeRole : MolecularRole
  h2AntagonistProbeRole : MolecularRole

record MolecularIdentityReceipt : Set where
  constructor molecularIdentityReceipt
  field
    commonName : String
    stableIdentifier : String
    molecularFormula : String
    role : MolecularRole
    source : Source.AttributedSource

    identityOnly : Bool
    identityOnlyIsTrue : identityOnly ≡ true

    targetActionImported : Bool
    targetActionImportedIsFalse : targetActionImported ≡ false

    doseResponseImported : Bool
    doseResponseImportedIsFalse : doseResponseImported ≡ false

    clinicalEffectImported : Bool
    clinicalEffectImportedIsFalse : clinicalEffectImported ≡ false

open MolecularIdentityReceipt public

pubChemHistamine : Source.AttributedSource
pubChemHistamine =
  Source.mkNoDOISource
    "PubChem"
    "Histamine | CID 774"
    "National Library of Medicine / PubChem"
    "2026"
    "https://pubchem.ncbi.nlm.nih.gov/compound/774"
    Source.institutionalSource
    "Molecular identity descriptor for histamine; identity does not import receptor, pathway, or PMDD authority."
    Source.publicAttribution

pubChemFexofenadine : Source.AttributedSource
pubChemFexofenadine =
  Source.mkNoDOISource
    "PubChem"
    "Fexofenadine | CID 3348"
    "National Library of Medicine / PubChem"
    "2026"
    "https://pubchem.ncbi.nlm.nih.gov/compound/3348"
    Source.institutionalSource
    "Molecular identity descriptor for fexofenadine; pharmacological and clinical effects are not imported by identity."
    Source.publicAttribution

pubChemFamotidine : Source.AttributedSource
pubChemFamotidine =
  Source.mkNoDOISource
    "PubChem"
    "Famotidine | CID 5702160"
    "National Library of Medicine / PubChem"
    "2026"
    "https://pubchem.ncbi.nlm.nih.gov/compound/5702160"
    Source.institutionalSource
    "Molecular identity descriptor for famotidine; pharmacological and clinical effects are not imported by identity."
    Source.publicAttribution

pubChemEstradiol : Source.AttributedSource
pubChemEstradiol =
  Source.mkNoDOISource
    "PubChem"
    "Estradiol | CID 5757"
    "National Library of Medicine / PubChem"
    "2026"
    "https://pubchem.ncbi.nlm.nih.gov/compound/5757"
    Source.institutionalSource
    "Molecular identity descriptor for 17beta-estradiol; mast-cell effects remain source-conditioned elsewhere."
    Source.publicAttribution

pubChemAllopregnanolone : Source.AttributedSource
pubChemAllopregnanolone =
  Source.mkNoDOISource
    "PubChem"
    "Allopregnanolone | CID 92786"
    "National Library of Medicine / PubChem"
    "2026"
    "https://pubchem.ncbi.nlm.nih.gov/compound/92786"
    Source.institutionalSource
    "Molecular identity descriptor for allopregnanolone; GABA_A modulation and PMDD interpretation remain separate source roles."
    Source.publicAttribution

histamineIdentity : MolecularIdentityReceipt
histamineIdentity =
  molecularIdentityReceipt
    "histamine"
    "PubChem CID 774"
    "C5H9N3"
    endogenousMediatorRole
    pubChemHistamine
    true refl
    false refl
    false refl
    false refl

fexofenadineIdentity : MolecularIdentityReceipt
fexofenadineIdentity =
  molecularIdentityReceipt
    "fexofenadine"
    "PubChem CID 3348"
    "C32H39NO4"
    h1AntagonistProbeRole
    pubChemFexofenadine
    true refl
    false refl
    false refl
    false refl

famotidineIdentity : MolecularIdentityReceipt
famotidineIdentity =
  molecularIdentityReceipt
    "famotidine"
    "PubChem CID 5702160"
    "C8H15N7O2S3"
    h2AntagonistProbeRole
    pubChemFamotidine
    true refl
    false refl
    false refl
    false refl

estradiolIdentity : MolecularIdentityReceipt
estradiolIdentity =
  molecularIdentityReceipt
    "17beta-estradiol"
    "PubChem CID 5757"
    "C18H24O2"
    ovarianSteroidRole
    pubChemEstradiol
    true refl
    false refl
    false refl
    false refl

allopregnanoloneIdentity : MolecularIdentityReceipt
allopregnanoloneIdentity =
  molecularIdentityReceipt
    "allopregnanolone"
    "PubChem CID 92786"
    "C21H34O2"
    neurosteroidRole
    pubChemAllopregnanolone
    true refl
    false refl
    false refl
    false refl

canonicalMolecularIdentities : List MolecularIdentityReceipt
canonicalMolecularIdentities =
  histamineIdentity
  ∷ fexofenadineIdentity
  ∷ famotidineIdentity
  ∷ estradiolIdentity
  ∷ allopregnanoloneIdentity
  ∷ []

------------------------------------------------------------------------
-- Target-context receipts.
------------------------------------------------------------------------

data HistamineTarget : Set where
  histamineH1Receptor : HistamineTarget
  histamineH2Receptor : HistamineTarget
  diamineOxidaseAOC1 : HistamineTarget
  gabaaReceptorContext : HistamineTarget
  mastCellEstrogenSensitiveContext : HistamineTarget

data TargetRelation : Set where
  endogenousLigandTargetCandidate : TargetRelation
  antagonistTargetCandidate : TargetRelation
  degradationEnzymeCandidate : TargetRelation
  allostericModulationContextCandidate : TargetRelation
  hormoneSensitiveCellContextCandidate : TargetRelation

record MolecularTargetCandidate : Set where
  constructor molecularTargetCandidate
  field
    molecule : MolecularIdentityReceipt
    target : HistamineTarget
    relation : TargetRelation
    sourceReference : String

    relationIsCandidateOnly : Bool
    relationIsCandidateOnlyIsTrue :
      relationIsCandidateOnly ≡ true

    efficacyEstablished : Bool
    efficacyEstablishedIsFalse :
      efficacyEstablished ≡ false

    clinicalPMDDMeaningEstablished : Bool
    clinicalPMDDMeaningEstablishedIsFalse :
      clinicalPMDDMeaningEstablished ≡ false

open MolecularTargetCandidate public

histamineH1Candidate : MolecularTargetCandidate
histamineH1Candidate =
  molecularTargetCandidate
    histamineIdentity
    histamineH1Receptor
    endogenousLigandTargetCandidate
    "Histamine/H1 target relation retained as a receptor-context candidate; quantitative occupancy and PMDD transfer require protocol authority."
    true refl false refl false refl

histamineH2Candidate : MolecularTargetCandidate
histamineH2Candidate =
  molecularTargetCandidate
    histamineIdentity
    histamineH2Receptor
    endogenousLigandTargetCandidate
    "Histamine/H2 target relation retained as a receptor-context candidate; quantitative occupancy and PMDD transfer require protocol authority."
    true refl false refl false refl

fexofenadineH1Candidate : MolecularTargetCandidate
fexofenadineH1Candidate =
  molecularTargetCandidate
    fexofenadineIdentity
    histamineH1Receptor
    antagonistTargetCandidate
    "PubChem classifies fexofenadine as an H1-receptor antagonist; this receipt does not import dose-response or PMDD efficacy."
    true refl false refl false refl

famotidineH2Candidate : MolecularTargetCandidate
famotidineH2Candidate =
  molecularTargetCandidate
    famotidineIdentity
    histamineH2Receptor
    antagonistTargetCandidate
    "PubChem describes famotidine as a competitive H2-receptor antagonist; this receipt does not import dose-response or PMDD efficacy."
    true refl false refl false refl

alloGABAACandidate : MolecularTargetCandidate
alloGABAACandidate =
  molecularTargetCandidate
    allopregnanoloneIdentity
    gabaaReceptorContext
    allostericModulationContextCandidate
    "GABA_A neurosteroid modulation is source-bound by the PMDD source atlas; molecular identity alone does not prove the mechanism."
    true refl false refl false refl

estradiolMastCellCandidate : MolecularTargetCandidate
estradiolMastCellCandidate =
  molecularTargetCandidate
    estradiolIdentity
    mastCellEstrogenSensitiveContext
    hormoneSensitiveCellContextCandidate
    "Estradiol/mast-cell relation is source-conditioned to Zaitsu et al. 2007 and is not promoted to an in-vivo PMDD theorem."
    true refl false refl false refl

canonicalTargetCandidates : List MolecularTargetCandidate
canonicalTargetCandidates =
  histamineH1Candidate
  ∷ histamineH2Candidate
  ∷ fexofenadineH1Candidate
  ∷ famotidineH2Candidate
  ∷ alloGABAACandidate
  ∷ estradiolMastCellCandidate
  ∷ []

------------------------------------------------------------------------
-- Existing generic target / atomic owners.
------------------------------------------------------------------------

atomicChemistryOwner :
  AtomicChem.NeurochemicalAtomicChemistryBridge
atomicChemistryOwner =
  AtomicChem.canonicalNeurochemicalAtomicChemistryBridge

proteinTargetOwner :
  ProteinTarget.NeurochemicalProteinTargetBridge
proteinTargetOwner =
  ProteinTarget.canonicalNeurochemicalProteinTargetBridge

------------------------------------------------------------------------
-- H1 + H2 intervention is a typed perturbation, not a diagnostic oracle.
------------------------------------------------------------------------

data InterventionChannel : Set where
  h1BlockadeChannel : InterventionChannel
  h2BlockadeChannel : InterventionChannel

record DualHistamineBlockadeCandidate : Set where
  constructor dualHistamineBlockadeCandidate
  field
    h1Probe : MolecularIdentityReceipt
    h2Probe : MolecularIdentityReceipt
    channels : List InterventionChannel

    distinctReceptorChannels : Bool
    distinctReceptorChannelsIsTrue :
      distinctReceptorChannels ≡ true

    perturbationCanTestHistamineDependence : Bool
    perturbationCanTestHistamineDependenceIsTrue :
      perturbationCanTestHistamineDependence ≡ true

    responseIdentifiesUniqueCause : Bool
    responseIdentifiesUniqueCauseIsFalse :
      responseIdentifiesUniqueCause ≡ false

    responseDiagnosesSubtype : Bool
    responseDiagnosesSubtypeIsFalse :
      responseDiagnosesSubtype ≡ false

    efficacyInPMDDEstablished : Bool
    efficacyInPMDDEstablishedIsFalse :
      efficacyInPMDDEstablished ≡ false

open DualHistamineBlockadeCandidate public

canonicalDualHistamineBlockadeCandidate :
  DualHistamineBlockadeCandidate
canonicalDualHistamineBlockadeCandidate =
  dualHistamineBlockadeCandidate
    fexofenadineIdentity
    famotidineIdentity
    (h1BlockadeChannel ∷ h2BlockadeChannel ∷ [])
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Gut / DAO lane: retained as a modifier candidate, not a root-cause theorem.
------------------------------------------------------------------------

record HistamineClearanceModifierCandidate : Set where
  constructor histamineClearanceModifierCandidate
  field
    clearanceTarget : HistamineTarget
    targetReading : String

    canModifyPeripheralHistamineExposure : Bool
    canModifyPeripheralHistamineExposureIsCandidate :
      canModifyPeripheralHistamineExposure ≡ true

    measuredInPMDDCohort : Bool
    measuredInPMDDCohortIsFalse :
      measuredInPMDDCohort ≡ false

    establishesGutRootCause : Bool
    establishesGutRootCauseIsFalse :
      establishesGutRootCause ≡ false

open HistamineClearanceModifierCandidate public

daoClearanceModifierCandidate :
  HistamineClearanceModifierCandidate
daoClearanceModifierCandidate =
  histamineClearanceModifierCandidate
    diamineOxidaseAOC1
    "DAO/AOC1 is retained only as a candidate intestinal/peripheral histamine-clearance coordinate pending source- and protocol-indexed PMDD measurements."
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Cross-scale weld to the parent hypothesis.
------------------------------------------------------------------------

record MolecularlyInstantiatedPMDDHistamineCandidate : Set where
  constructor molecularlyInstantiatedPMDDHistamineCandidate
  field
    parent : PMDD.HistamineAmplifiedPMDDCandidate
    molecules : List MolecularIdentityReceipt
    targets : List MolecularTargetCandidate
    intervention : DualHistamineBlockadeCandidate
    clearanceModifier : HistamineClearanceModifierCandidate
    atomicOwner : AtomicChem.NeurochemicalAtomicChemistryBridge
    targetOwner : ProteinTarget.NeurochemicalProteinTargetBridge

    molecularLayerConcrete : Bool
    molecularLayerConcreteIsTrue :
      molecularLayerConcrete ≡ true

    receptorContextConcrete : Bool
    receptorContextConcreteIsTrue :
      receptorContextConcrete ≡ true

    occupancyCalibrationPresent : Bool
    occupancyCalibrationPresentIsFalse :
      occupancyCalibrationPresent ≡ false

    pmddClinicalTransferPresent : Bool
    pmddClinicalTransferPresentIsFalse :
      pmddClinicalTransferPresent ≡ false

open MolecularlyInstantiatedPMDDHistamineCandidate public

canonicalMolecularlyInstantiatedPMDDHistamineCandidate :
  MolecularlyInstantiatedPMDDHistamineCandidate
canonicalMolecularlyInstantiatedPMDDHistamineCandidate =
  molecularlyInstantiatedPMDDHistamineCandidate
    PMDD.canonicalHistamineAmplifiedPMDDCandidate
    canonicalMolecularIdentities
    canonicalTargetCandidates
    canonicalDualHistamineBlockadeCandidate
    daoClearanceModifierCandidate
    atomicChemistryOwner
    proteinTargetOwner
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Anti-collapse.
------------------------------------------------------------------------

data MolecularIdentityDeterminesPMDDResponse : Set where
data H1H2TargetPairProvesPMDDEfficacy : Set where
data DAOCandidateProvesGutCause : Set where
data AntagonistClassificationDeterminesDose : Set where

molecularIdentityDoesNotDeterminePMDDResponse :
  MolecularIdentityDeterminesPMDDResponse → ⊥
molecularIdentityDoesNotDeterminePMDDResponse ()

h1h2TargetPairDoesNotProvePMDDEfficacy :
  H1H2TargetPairProvesPMDDEfficacy → ⊥
h1h2TargetPairDoesNotProvePMDDEfficacy ()

daoCandidateDoesNotProveGutCause :
  DAOCandidateProvesGutCause → ⊥
daoCandidateDoesNotProveGutCause ()

antagonistClassificationDoesNotDetermineDose :
  AntagonistClassificationDeterminesDose → ⊥
antagonistClassificationDoesNotDetermineDose ()
