module DASHI.Biology.QuailEggOralGIAnimalBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Source

lianto2018EoESource : Source.AttributedSource
lianto2018EoESource = Source.mkDOISource
  "Priscilia Lianto; Shiwen Han; Xinrui Li; Fredrick Onyango Ogutu; Yani Zhang; Zhuoyan Fan; Huilian Che"
  "Quail egg homogenate alleviates food allergy induced eosinophilic esophagitis like disease through modulating PAR-2 transduction pathway in peanut sensitized mice"
  "Scientific Reports 8:1049" "2018"
  "10.1038/s41598-018-19309-x" "https://doi.org/10.1038/s41598-018-19309-x"
  Source.academicArticleSource
  "Pays daily oral whole-quail-egg intervention evidence in a peanut-sensitized mouse EoE-like food-allergy model, with bounded symptom, tryptase/eosinophil, immunoglobulin, cytokine and PAR-2/NF-kB-related outcomes. It does not pay human IBS efficacy."
  Source.publicAttribution

record QuailOralGIAnimalReceipt : Set where
  constructor quail-oral-gi-animal-receipt
  field source : Source.AttributedSource
        oralWholeQuailExposure : Bool
        gastrointestinalInflammatoryModel : Bool
        tryptaseOrEosinophilEndpoints : Bool
        par2NFkBPathwayEvidence : Bool
        humanPopulation : Bool
        ibsPopulation : Bool
        boundary : String

lianto2018EoEReceipt : QuailOralGIAnimalReceipt
lianto2018EoEReceipt = quail-oral-gi-animal-receipt
  lianto2018EoESource true true true true false false
  "This pays oral GI exposure in an animal disease model and narrows the transfer gap beyond isolated cell assays; species, disease model, allergen sensitization, dose and IBS phenotype transfer remain open."

data MouseEoEEvidencePaysHumanIBSPermission : Set where
mouseEoEDoesNotPayHumanIBS : MouseEoEEvidencePaysHumanIBSPermission → ⊥
mouseEoEDoesNotPayHumanIBS ()

data MouseOralExposurePaysHumanTargetEngagementPermission : Set where
mouseOralDoesNotPayHumanTargetEngagement : MouseOralExposurePaysHumanTargetEngagementPermission → ⊥
mouseOralDoesNotPayHumanTargetEngagement ()

record QuailOralGIAnimalBoundary : Set where
  constructor quail-oral-gi-animal-boundary
  field oralGIAnimalExposurePaid : Bool
        oralGIAnimalExposurePaidIsTrue : oralGIAnimalExposurePaid ≡ true
        par2PathwayAnimalEvidencePaid : Bool
        par2PathwayAnimalEvidencePaidIsTrue : par2PathwayAnimalEvidencePaid ≡ true
        humanGIExposurePaidByThisStudy : Bool
        humanGIExposurePaidByThisStudyIsFalse : humanGIExposurePaidByThisStudy ≡ false
        humanIBSEfficacyPaid : Bool
        humanIBSEfficacyPaidIsFalse : humanIBSEfficacyPaid ≡ false

canonicalQuailOralGIAnimalBoundary : QuailOralGIAnimalBoundary
canonicalQuailOralGIAnimalBoundary = quail-oral-gi-animal-boundary
  true refl true refl false refl false refl
