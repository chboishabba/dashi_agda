module DASHI.Biology.JasonThomasSTINGFerritinophagyMechanismDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Jason R. Thomas appears on both Koch et al. 2018 STING/IRF3/NFkB screening
-- and Dowdle et al. 2014 VPS34/NCOA4 ferritinophagy work.

data STINGStage : Set where
  stimulus
  STINGPathway
  IRF3Translocation
  NFkBTranslocation
  downstreamCytokineReadout
  kinaseTargetDeconvolution
  chemicalProteomics
  geneticValidation
  : STINGStage

data FerritinophagyStage : Set where
  VPS34Activity
  autophagosomeFormation
  NCOA4CargoRecognition
  ferritinDelivery
  lysosomalDegradation
  ironRelease
  ironHomeostasis
  : FerritinophagyStage

record STINGAssayLogic : Set where
  constructor sting-assay-logic
  field
    primaryPhenotype : String
    downstreamCountercheck : String
    targetDeconvolution : String
    unresolvedAlternative : String
    sourceReference : String

open STINGAssayLogic public

canonicalSTINGAssayLogic : STINGAssayLogic
canonicalSTINGAssayLogic = sting-assay-logic
  "high-content imaging of IRF3 and NFkB cytoplasm-to-nucleus translocation in primary human macrophages"
  "majority of activator-screen translocation hits did not activate downstream pathways"
  "mini-SAR plus lysate-based chemical proteomics implicated MAPKAPK5/PRAK"
  "MAPKAPK2 could not be decisively excluded; ideal genetic knockout or inhibitor-resistant rescue was difficult in primary macrophages"
  "Koch et al. ACS Chem Biol 2018, DOI 10.1021/acschembio.7b01060"

record FerritinophagyLogic : Set where
  constructor ferritinophagy-logic
  field
    perturbation : String
    substrateDiscovery : String
    cargoReceptorReading : String
    traffickingConsequence : String
    ironConsequence : String
    sourceReference : String

open FerritinophagyLogic public

canonicalFerritinophagyLogic : FerritinophagyLogic
canonicalFerritinophagyLogic = ferritinophagy-logic
  "selective VPS34 inhibition with PIK-III blocks autophagy"
  "NCOA4 accumulates as an autophagy substrate and was linked to ferritin turnover"
  "NCOA4 is required for ferritin delivery to lysosomal/autophagic degradation machinery"
  "blocking the pathway stabilises ferritin and prevents normal ferritin turnover"
  "reduced ferritin turnover perturbs bioavailable intracellular iron / iron homeostasis"
  "Dowdle et al. Nat Cell Biol 2014, DOI 10.1038/ncb3053"

record ThomasMechanismDepthBoundary : Set where
  constructor thomas-mechanism-depth-boundary
  field
    translocationHitIsDownstreamActivation : Bool
    translocationHitIsDownstreamActivationIsFalse : translocationHitIsDownstreamActivation ≡ false
    chemicalProteomicsBindingProvesUniqueEfficacyTarget : Bool
    chemicalProteomicsBindingProvesUniqueEfficacyTargetIsFalse : chemicalProteomicsBindingProvesUniqueEfficacyTarget ≡ false
    VPS34InhibitionMeansNCOA4IsDirectVPS34Substrate : Bool
    VPS34InhibitionMeansNCOA4IsDirectVPS34SubstrateIsFalse : VPS34InhibitionMeansNCOA4IsDirectVPS34Substrate ≡ false
    NCOA4FerritinPathwaySupportsFerritinIronReleaseMechanism : Bool
    NCOA4FerritinPathwaySupportsFerritinIronReleaseMechanismIsTrue : NCOA4FerritinPathwaySupportsFerritinIronReleaseMechanism ≡ true

canonicalThomasMechanismDepthBoundary : ThomasMechanismDepthBoundary
canonicalThomasMechanismDepthBoundary = thomas-mechanism-depth-boundary false refl false refl false refl true refl

data ThomasReverseTarget : Set where
  acquirePrimaryImageThresholds
  acquireDownstreamCytokineAssay
  acquireKinaseSelectivityPanel
  acquireChemicalProteomicsCompetition
  acquireGeneticPerturbation
  acquireVPS34SelectivityReceipt
  acquireNCOA4FerritinBindingReceipt
  acquireLysosomalDeliveryReceipt
  acquireIronAvailabilityReadout
  : ThomasReverseTarget
