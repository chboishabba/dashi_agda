module DASHI.Biology.KitzerowBH4HepaticCompetitionDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Chemistry.LineageAcquiredPrimaryEvidenceExact as Evidence
import DASHI.Biology.KitzerowBH4FluxCausalModelsExact as Flux

------------------------------------------------------------------------
-- SAME-SYSTEM TWO-BRANCH BH4 ALLOCATION DISCRIMINATOR
--
-- Pastor et al. 1996 explicitly tested whether PAH and induced NOS compete for
-- BH4 in C. parvum-stimulated rat liver/hepatocytes.  This is substantially
-- stronger for the allocator question than separate pathway papers because
-- BH4, PAH output and NOS output are perturbed/read in the same biological
-- system.  The result is conditional rather than a simple positive allocator
-- result: under adequate de-novo synthesis there is little evidence of strong
-- competition; when GTP cyclohydrolase-I/BH4 synthesis is inhibited by DAHP,
-- increased PAH demand can suppress NO output, and exogenous BH4 rescues the
-- constrained system.
------------------------------------------------------------------------

source : Source.AttributedSource
source = Evidence.bh4HepaticCompetition1996

data HepatocyteCondition : Set where
  basal phe dahp pheDahp bh4 pheBh4 pheBh4Dahp : HepatocyteCondition

record HepatocyteOutputReceipt : Set where
  constructor hepatocyteOutputReceipt
  field
    condition : HepatocyteCondition
    substrateReference : String
    noxSupernatant : String
    tyrosineSupernatant : String
    unitReference : String
    sourceLocator : String

open HepatocyteOutputReceipt public

basalOutput pheOutput dahpOutput pheDahpOutput bh4Output pheBh4Output pheBh4DahpOutput : HepatocyteOutputReceipt
basalOutput = hepatocyteOutputReceipt basal "0.5 mM arginine background; no listed added substrate" "2373 +/- 90" "134 +/- 23" "nmol / 4.5 x 10^6 cells / 24 h" "Pastor et al. 1996 Table I"
pheOutput = hepatocyteOutputReceipt phe "0.5 mM phenylalanine" "2493 +/- 303" "678 +/- 156" "nmol / 4.5 x 10^6 cells / 24 h" "Pastor et al. 1996 Table I"
dahpOutput = hepatocyteOutputReceipt dahp "10 mM DAHP" "2080 +/- 313" "126 +/- 5" "nmol / 4.5 x 10^6 cells / 24 h" "Pastor et al. 1996 Table I"
pheDahpOutput = hepatocyteOutputReceipt pheDahp "0.5 mM phenylalanine + 10 mM DAHP" "1069 +/- 228" "150 +/- 6" "nmol / 4.5 x 10^6 cells / 24 h" "Pastor et al. 1996 Table I"
bh4Output = hepatocyteOutputReceipt bh4 "100 uM BH4" "3236 +/- 323" "143 +/- 8" "nmol / 4.5 x 10^6 cells / 24 h" "Pastor et al. 1996 Table I"
pheBh4Output = hepatocyteOutputReceipt pheBh4 "0.5 mM phenylalanine + 100 uM BH4" "3653 +/- 343" "465 +/- 63" "nmol / 4.5 x 10^6 cells / 24 h" "Pastor et al. 1996 Table I"
pheBh4DahpOutput = hepatocyteOutputReceipt pheBh4Dahp "0.5 mM phenylalanine + 100 uM BH4 + 10 mM DAHP" "3536 +/- 545" "709 +/- 26" "nmol / 4.5 x 10^6 cells / 24 h" "Pastor et al. 1996 Table I"

canonicalHepatocyteOutputs : List HepatocyteOutputReceipt
canonicalHepatocyteOutputs = basalOutput ∷ pheOutput ∷ dahpOutput ∷ pheDahpOutput ∷ bh4Output ∷ pheBh4Output ∷ pheBh4DahpOutput ∷ []

record HepatocytePterinReceipt : Set where
  constructor hepatocytePterinReceipt
  field
    conditionReference : String
    cellularBH4 : String
    totalBiopterinCells : String
    totalBiopterinSupernatant : String
    unitReference : String
    sourceLocator : String

open HepatocytePterinReceipt public

basalPterin phePterin dahpPterin pheDahpPterin : HepatocytePterinReceipt
basalPterin = hepatocytePterinReceipt "none" "19.2 +/- 1.4" "31.8 +/- 4.3" "4.9 +/- 0.9" "pmol/mg protein" "Pastor et al. 1996 Table II"
phePterin = hepatocytePterinReceipt "0.5 mM phenylalanine" "17.0 +/- 0.7" "29.1 +/- 2.9" "20.6 +/- 2.4" "pmol/mg protein" "Pastor et al. 1996 Table II"
dahpPterin = hepatocytePterinReceipt "10 mM DAHP" "1.8 +/- 0.1" "5.1 +/- 1.0" "0.6 +/- 0.3" "pmol/mg protein" "Pastor et al. 1996 Table II"
pheDahpPterin = hepatocytePterinReceipt "0.5 mM phenylalanine + 10 mM DAHP" "1.0 +/- 0.4" "3.8 +/- 0.6" "not determined" "pmol/mg protein" "Pastor et al. 1996 Table II"

canonicalHepatocytePterins : List HepatocytePterinReceipt
canonicalHepatocytePterins = basalPterin ∷ phePterin ∷ dahpPterin ∷ pheDahpPterin ∷ []

record HepaticCompetitionDiscriminator : Set where
  constructor hepaticCompetitionDiscriminator
  field
    sourceReference : Source.AttributedSource
    targetCausalModelReference : String
    biologicalSystem : String
    pahReadout : String
    inosReadout : String
    poolReadout : String
    supplyPerturbation : String
    demandPerturbation : String
    rescuePerturbation : String
    adequateSupplyResult : String
    constrainedSupplyResult : String
    adaptiveSupplyResult : String
    causalInterpretation : String
    remainingConsumer : String

open HepaticCompetitionDiscriminator public

canonicalHepaticCompetitionDiscriminator : HepaticCompetitionDiscriminator
canonicalHepaticCompetitionDiscriminator =
  hepaticCompetitionDiscriminator
    source
    "KitzerowBH4FluxCausalModelsExact: H1 upstream allocator versus H4 context-specific mechanism"
    "C. parvum-stimulated rat isolated perfused liver and cultured hepatocytes expressing high iNOS alongside hepatic PAH"
    "phenylalanine -> tyrosine output"
    "NO2- + NO3- output"
    "cellular BH4 plus total biopterin in cells/supernatant"
    "10 mM DAHP inhibits GTP cyclohydrolase-I / de-novo BH4 synthesis"
    "phenylalanine increases PAH demand; arginine increases NOS substrate supply"
    "100 uM exogenous BH4"
    "little evidence that maximizing either PAH or iNOS flux strongly limits the other while de-novo BH4 supply is available"
    "with DAHP-constrained BH4 synthesis, phenylalanine demand sharply lowers NOx output and tyrosine production is also supply-sensitive"
    "phenylalanine markedly increases biopterin release/synthesis response, consistent with adaptive supply buffering PAH demand"
    "rejects a naive fixed-pool strong-competition reading in this hepatic context while supporting a conditional supply-limited competition mechanism when BH4 synthesis is constrained"
    "does not determine TH/TPH/AGMO allocation, neural cell contexts, human disease subgroups, developmental timing or the whole Kitzerow causal architecture"

record HepaticCompetitionBoundary : Set where
  constructor hepaticCompetitionBoundary
  field
    sameSystemPAHAndINOSMeasured : Bool
    sameSystemPAHAndINOSMeasuredIsTrue : sameSystemPAHAndINOSMeasured ≡ true
    cellularBH4Measured : Bool
    cellularBH4MeasuredIsTrue : cellularBH4Measured ≡ true
    strongCompetitionAtAdequateSynthesisSupported : Bool
    strongCompetitionAtAdequateSynthesisSupportedIsFalse : strongCompetitionAtAdequateSynthesisSupported ≡ false
    conditionalCompetitionWhenBH4SynthesisBlocked : Bool
    conditionalCompetitionWhenBH4SynthesisBlockedIsTrue : conditionalCompetitionWhenBH4SynthesisBlocked ≡ true
    exogenousBH4RescuesConstrainedSystem : Bool
    exogenousBH4RescuesConstrainedSystemIsTrue : exogenousBH4RescuesConstrainedSystem ≡ true
    phenylalanineInducesBiopterinSupplyResponse : Bool
    phenylalanineInducesBiopterinSupplyResponseIsTrue : phenylalanineInducesBiopterinSupplyResponse ≡ true
    hepaticTwoBranchResultProvesWholeBH4AllocatorModel : Bool
    hepaticTwoBranchResultProvesWholeBH4AllocatorModelIsFalse : hepaticTwoBranchResultProvesWholeBH4AllocatorModel ≡ false
    hepaticResultGeneralizesToHumanNeurobiology : Bool
    hepaticResultGeneralizesToHumanNeurobiologyIsFalse : hepaticResultGeneralizesToHumanNeurobiology ≡ false
    hepaticResultPaysTH_TPH_AGMO : Bool
    hepaticResultPaysTH_TPH_AGMOIsFalse : hepaticResultPaysTH_TPH_AGMO ≡ false
    directSameSystemEvidenceOutranksSeparatePathwayAnalogy : Bool
    directSameSystemEvidenceOutranksSeparatePathwayAnalogyIsTrue : directSameSystemEvidenceOutranksSeparatePathwayAnalogy ≡ true

open HepaticCompetitionBoundary public

canonicalHepaticCompetitionBoundary : HepaticCompetitionBoundary
canonicalHepaticCompetitionBoundary =
  hepaticCompetitionBoundary
    true refl true refl false refl true refl true refl true refl
    false refl false refl false refl true refl
