module DASHI.Chemistry.AlliumOrganosulfurMechanismExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ALLIUM ORGANOSULFUR MOLECULAR-MECHANISM RECEIPTS
--
-- Source anchors:
--   Rabinkov et al. 1998, BBA 1379:233-244.
--     DOI 10.1016/S0304-4165(97)00104-9
--   Borlinghaus et al. 2014, Molecules 19:12591-12618.
--     PMID 25153873
--   Borlinghaus et al. 2021, Molecules 26:1505.
--     PMID 33801955 / PMCID PMC8001868
--   Fong et al. 2017, J Med Chem 60:215-227.
--     DOI 10.1021/acs.jmedchem.6b01025
--
-- These sources support a partial mechanism graph.  They do not establish an
-- exhaustive molecular account of any historical multi-ingredient remedy.
------------------------------------------------------------------------

data OrganosulfurCompound : Set where
  alliin
  allicin
  ajoene
  diallylDisulfide
  diallylTrisulfide
  : OrganosulfurCompound

data MolecularActionKind : Set where
  alliinaseConversion
  membraneEntry
  thiolReaction
  sThioallylation
  lowMolecularWeightThiolDepletion
  enzymeInhibition
  redoxStress
  regulatoryRNAModulation
  quorumRegulationInterference
  : MolecularActionKind

data EvidenceRelation : Set where
  directChemicalReaction
  biochemicalTargetEvidence
  proteomicEvidence
  reporterAssayEvidence
  reviewSynthesis
  inferredPathwayBridge
  : EvidenceRelation

record MolecularActionReceipt : Set where
  constructor molecularActionReceipt
  field
    compound : OrganosulfurCompound
    action : MolecularActionKind
    targetReference : String
    organismReference : String
    relation : EvidenceRelation
    sourceReference : String
    assayReference : String
    scopeBoundary : String

open MolecularActionReceipt public

allicinThiolReceipt : MolecularActionReceipt
allicinThiolReceipt =
  molecularActionReceipt
    allicin
    thiolReaction
    "accessible cysteine/protein thiols and low-molecular-weight thiols"
    "cross-system chemical mechanism; organism-specific effects remain indexed"
    directChemicalReaction
    "Rabinkov et al. 1998 DOI 10.1016/S0304-4165(97)00104-9; Borlinghaus et al. 2021 PMID 33801955"
    "NMR / thiol-reactivity / cellular redox literature"
    "supports thiol reactivity; does not enumerate every in-cell target"

allicinSThioallylationReceipt : MolecularActionReceipt
allicinSThioallylationReceipt =
  molecularActionReceipt
    allicin
    sThioallylation
    "accessible cysteine residues in proteins"
    "bacterial and eukaryotic cells represented in the review literature"
    proteomicEvidence
    "Borlinghaus et al. 2021 PMID 33801955"
    "redox-proteomic and biochemical evidence"
    "target coverage is partial and context dependent"

allicinRedoxReceipt : MolecularActionReceipt
allicinRedoxReceipt =
  molecularActionReceipt
    allicin
    lowMolecularWeightThiolDepletion
    "glutathione in Gram-negative bacteria; bacillithiol in Gram-positive Firmicutes"
    "organism-indexed"
    reviewSynthesis
    "Borlinghaus et al. 2021 PMID 33801955"
    "cellular redox literature"
    "redox disturbance is one causal lane, not a complete phenotype explanation"

ajoeneQSReceipt : MolecularActionReceipt
ajoeneQSReceipt =
  molecularActionReceipt
    ajoene
    regulatoryRNAModulation
    "Gac/Rsm-associated small regulatory RNAs including RsmY/RsmZ in Pseudomonas aeruginosa"
    "Pseudomonas aeruginosa"
    reporterAssayEvidence
    "Fong et al. 2017 DOI 10.1021/acs.jmedchem.6b01025; related Jakobsen/Givskov quorum-sensing literature"
    "quorum-sensing bioreporter / gene-expression assays"
    "supports an anti-QS lane for ajoene-like compounds; does not establish that Bald's eyesalve acts principally through this route"

record MolecularMechanismBoundary : Set where
  constructor molecularMechanismBoundary
  field
    principalActiveCompoundEqualsCompleteMechanism : Bool
    principalActiveCompoundEqualsCompleteMechanismIsFalse :
      principalActiveCompoundEqualsCompleteMechanism ≡ false

    oneKnownTargetImpliesExhaustiveTargetSet : Bool
    oneKnownTargetImpliesExhaustiveTargetSetIsFalse :
      oneKnownTargetImpliesExhaustiveTargetSet ≡ false

    garlicQuorumActivityProvesHistoricalMixtureQSMechanism : Bool
    garlicQuorumActivityProvesHistoricalMixtureQSMechanismIsFalse :
      garlicQuorumActivityProvesHistoricalMixtureQSMechanism ≡ false

    thiolReactivityProvesUniquePhenotypicPathway : Bool
    thiolReactivityProvesUniquePhenotypicPathwayIsFalse :
      thiolReactivityProvesUniquePhenotypicPathway ≡ false

    mechanismGraphIsCurrentlyPartial : Bool
    mechanismGraphIsCurrentlyPartialIsTrue :
      mechanismGraphIsCurrentlyPartial ≡ true

canonicalMolecularMechanismBoundary : MolecularMechanismBoundary
canonicalMolecularMechanismBoundary =
  molecularMechanismBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
