module DASHI.Biology.Protein.StaphylococcusAllicinThiolomeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- STAPHYLOCOCCUS AUREUS ALLICIN THIOLOME
--
-- Source anchor:
--   Loi et al. 2019, Free Radic Biol Med 139:55-69.
--   DOI 10.1016/j.freeradbiomed.2019.05.018 / PMID 31121222.
--
-- Directly relevant tangential evidence: S. aureus itself was exposed to
-- allicin, 57 S-thioallylated proteins were identified, and bacillithiol /
-- BrxAB / YpdA / MerA detoxification pathways were experimentally implicated.
-- This is stronger than cross-organism analogy but still is not a direct assay
-- of the complete Bald's-eyesalve mixture.
------------------------------------------------------------------------

data ProteinClass : Set where
  translationFactor
  metabolicEnzyme
  redoxEnzyme
  transcriptionalRegulator
  antioxidantEnzyme
  detoxificationProtein
  : ProteinClass

record ProteinTargetReceipt : Set where
  constructor proteinTargetReceipt
  field
    proteinName : String
    proteinClass : ProteinClass
    modification : String
    cysteineReference : String
    functionalContext : String
    sourceReference : String
    directSAureusEvidence : Bool

open ProteinTargetReceipt public

efTuTarget : ProteinTargetReceipt
efTuTarget = proteinTargetReceipt
  "EF-Tu"
  translationFactor
  "S-thioallylation under allicin exposure"
  "conserved cysteine target reported in S. aureus / related bacterial thiolomes"
  "translation machinery"
  "Loi et al. 2019 DOI 10.1016/j.freeradbiomed.2019.05.018"
  true

guaBTarget : ProteinTargetReceipt
guaBTarget = proteinTargetReceipt
  "GuaB"
  metabolicEnzyme
  "S-thioallylation under allicin exposure"
  "redox-sensitive/conserved cysteine context"
  "IMP dehydrogenase / nucleotide metabolism"
  "Loi et al. 2019 DOI 10.1016/j.freeradbiomed.2019.05.018"
  true

katATarget : ProteinTargetReceipt
katATarget = proteinTargetReceipt
  "KatA"
  antioxidantEnzyme
  "S-thioallylation under allicin exposure"
  "target-site detail remains source-indexed"
  "oxidative-stress defence"
  "Loi et al. 2019 DOI 10.1016/j.freeradbiomed.2019.05.018"
  true

mgrATarget : ProteinTargetReceipt
mgrATarget = proteinTargetReceipt
  "MgrA"
  transcriptionalRegulator
  "S-thioallylation under allicin exposure"
  "redox-sensing cysteine context"
  "MarR/SarA-family regulatory response"
  "Loi et al. 2019 DOI 10.1016/j.freeradbiomed.2019.05.018"
  true

sarATarget : ProteinTargetReceipt
sarATarget = proteinTargetReceipt
  "SarA"
  transcriptionalRegulator
  "S-thioallylation under allicin exposure"
  "redox-sensitive regulatory cysteine context"
  "virulence/biofilm-associated transcriptional regulation is downstream and context dependent"
  "Loi et al. 2019 DOI 10.1016/j.freeradbiomed.2019.05.018"
  true

record ThiolHomeostasisReceipt : Set where
  constructor thiolHomeostasisReceipt
  field
    component : String
    role : String
    observedUnderAllicinStress : Bool
    sourceReference : String

open ThiolHomeostasisReceipt public

bacillithiolReceipt : ThiolHomeostasisReceipt
bacillithiolReceipt = thiolHomeostasisReceipt
  "bacillithiol (BSH)"
  "low-molecular-weight thiol buffer; allicin stress shifts BSH redox potential"
  true
  "Loi et al. 2019 PMID 31121222"

ypdAReceipt : ThiolHomeostasisReceipt
ypdAReceipt = thiolHomeostasisReceipt
  "YpdA"
  "BSSB reductase; uses S-allylmercaptobacillithiol-related substrate chemistry to regenerate BSH"
  true
  "Loi et al. 2019 PMID 31121222"

brxReceipt : ThiolHomeostasisReceipt
brxReceipt = thiolHomeostasisReceipt
  "BrxAB / BSH pathway"
  "participates in reversal of protein S-thioallylation"
  true
  "Loi et al. 2019 PMID 31121222"

merAReceipt : ThiolHomeostasisReceipt
merAReceipt = thiolHomeostasisReceipt
  "MerA disulfide reductase"
  "HypR-controlled disulfide-stress detoxification contribution"
  true
  "Loi et al. 2019 PMID 31121222"

record StaphylococcusAllicinBoundary : Set where
  constructor staphylococcusAllicinBoundary
  field
    fiftySevenModifiedProteinsMeansFiftySevenUniquePhenotypicCauses : Bool
    fiftySevenModifiedProteinsMeansFiftySevenUniquePhenotypicCausesIsFalse :
      fiftySevenModifiedProteinsMeansFiftySevenUniquePhenotypicCauses ≡ false

    proteinModificationProvesFunctionalInhibition : Bool
    proteinModificationProvesFunctionalInhibitionIsFalse :
      proteinModificationProvesFunctionalInhibition ≡ false

    regulatorModificationProvesQuorumMechanism : Bool
    regulatorModificationProvesQuorumMechanismIsFalse :
      regulatorModificationProvesQuorumMechanism ≡ false

    directSAureusAllicinEvidenceCanRefineEyesalveMechanismCandidates : Bool
    directSAureusAllicinEvidenceCanRefineEyesalveMechanismCandidatesIsTrue :
      directSAureusAllicinEvidenceCanRefineEyesalveMechanismCandidates ≡ true

    detoxificationResponseImpliesAllicinExposureIsDynamicCompetition : Bool
    detoxificationResponseImpliesAllicinExposureIsDynamicCompetitionIsTrue :
      detoxificationResponseImpliesAllicinExposureIsDynamicCompetition ≡ true

canonicalStaphylococcusAllicinBoundary : StaphylococcusAllicinBoundary
canonicalStaphylococcusAllicinBoundary = staphylococcusAllicinBoundary
  false refl false refl false refl true refl true refl
