module DASHI.Economics.AICoreWeaveGPUGenerationCadence20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact as AssetLife

------------------------------------------------------------------------
-- COREWEAVE GPU FRONTIER-GENERATION CADENCE
--
-- Public product/deployment milestones recover the cadence with which newer
-- accelerator generations reached CoreWeave. This is evidence about frontier
-- turnover pressure, not an installed-fleet retirement schedule. Older systems
-- can remain productive, be redeployed, or coexist with newer generations.
------------------------------------------------------------------------

companyPublicationKind : Source.SourceKind
companyPublicationKind = Source.namedSourceKind "primary company publication"

h100Source : Source.AttributedSource
h100Source = Source.mkNoDOISource
  "CoreWeave"
  "CoreWeave Announces NovelAI as Among the First to Have NVIDIA HGX H100 GPUs Online"
  "CoreWeave"
  "2023-03-21"
  "https://www.coreweave.com/blog/coreweave-announces-novelai-as-among-the-first-to-have-nvidia-hgx-h100-gpus-online"
  companyPublicationKind
  "primary carrier for H100 online/general-availability timing"
  Source.publicAttribution

h200Source : Source.AttributedSource
h200Source = Source.mkNoDOISource
  "CoreWeave"
  "CoreWeave Is the First Cloud Provider to Deploy NVIDIA H200 Tensor Core GPUs"
  "CoreWeave"
  "2024-08-28"
  "https://www.coreweave.com/blog/coreweave-is-the-first-cloud-provider-to-deploy-nvidia-h200-tensor-core-gpus"
  companyPublicationKind
  "primary carrier for H200 deployment timing"
  Source.publicAttribution

gb200Source : Source.AttributedSource
gb200Source = Source.mkNoDOISource
  "CoreWeave"
  "CoreWeave Becomes the First Cloud Provider with Generally Available NVIDIA GB200 NVL72 Instances"
  "CoreWeave"
  "2025-02-04"
  "https://www.coreweave.com/blog/coreweave-becomes-the-first-cloud-provider-with-generally-available-nvidia-gb200-nvl72-instances"
  companyPublicationKind
  "primary carrier for GB200 general-availability timing"
  Source.publicAttribution

gb300Source : Source.AttributedSource
gb300Source = Source.mkNoDOISource
  "CoreWeave"
  "CoreWeave Becomes First Cloud Provider to Deploy NVIDIA GB300 NVL72 Platform"
  "CoreWeave"
  "2025-07-03"
  "https://coreweave.com/news/coreweave-becomes-first-cloud-provider-to-deploy-nvidia-gb300-nvl72-platform"
  companyPublicationKind
  "primary carrier for GB300 customer-deployment timing"
  Source.publicAttribution

rubinSource : Source.AttributedSource
rubinSource = Source.mkNoDOISource
  "CoreWeave"
  "CoreWeave Delivers NVIDIA Vera Rubin NVL72 Performance at Production Scale"
  "CoreWeave"
  "2026-09-30"
  "https://www.coreweave.com/news/coreweave-delivers-nvidia-vera-rubin-nvl72-performance-at-production-scale-starting-with-cognition"
  companyPublicationKind
  "primary carrier for Vera Rubin production-workload timing and hundreds of Rubin GPUs deployed across multiple regions"
  Source.publicAttribution

record FrontierCadenceObservation : Set where
  constructor frontier-cadence-observation
  field
    company : String
    selectedTransitionH100ToH200Months : Nat
    selectedTransitionH200ToGB200Months : Nat
    selectedTransitionGB200ToGB300Months : Nat
    selectedTransitionGB300ToRubinProductionMonths : Nat
    selectedMeanTransitionTenthsMonths : Nat
    selectedMaxTransitionMonths : Nat
    accountingLifeMonths : Nat
    frontierSuccessorArrivesBeforeBookLife : Bool
    generationCadenceDeterminesRetirementCadence : Bool
    generationCadenceDeterminesEconomicObsolescence : Bool
    catalogPresenceDeterminesInstalledCount : Bool

open FrontierCadenceObservation public

coreWeaveSelectedFrontierCadence : FrontierCadenceObservation
coreWeaveSelectedFrontierCadence = frontier-cadence-observation
  "CoreWeave"
  17 6 5 14
  105
  17
  (AssetLife.currentUsefulLifeMonths AssetLife.coreWeaveTechnologyEquipmentLife)
  true false false false

selectedMaxTransitionMonthsIs17 :
  selectedMaxTransitionMonths coreWeaveSelectedFrontierCadence ≡ 17
selectedMaxTransitionMonthsIs17 = refl

selectedMeanTransitionTenthsMonthsIs105 :
  selectedMeanTransitionTenthsMonths coreWeaveSelectedFrontierCadence ≡ 105
selectedMeanTransitionTenthsMonthsIs105 = refl

frontierCadenceShorterThanBookLife :
  frontierSuccessorArrivesBeforeBookLife coreWeaveSelectedFrontierCadence ≡ true
frontierCadenceShorterThanBookLife = refl

data GenerationCadenceImpliesRetirementCadencePermission : Set where
data NewGenerationImpliesPriorGenerationObsoletePermission : Set where
data CatalogPresenceImpliesInstalledFleetSharePermission : Set where

generationCadenceDoesNotDetermineRetirementCadence :
  GenerationCadenceImpliesRetirementCadencePermission → ⊥
generationCadenceDoesNotDetermineRetirementCadence ()

newGenerationDoesNotAutoObsoletePriorGeneration :
  NewGenerationImpliesPriorGenerationObsoletePermission → ⊥
newGenerationDoesNotAutoObsoletePriorGeneration ()

catalogPresenceDoesNotDetermineInstalledFleetShare :
  CatalogPresenceImpliesInstalledFleetSharePermission → ⊥
catalogPresenceDoesNotDetermineInstalledFleetShare ()

boundary : String
boundary =
  "Selected CoreWeave public milestones give H100->H200 ~17 months, H200->GB200 ~6 months, GB200->GB300 ~5 months and GB300->Rubin-production ~14 months, versus a 72-month accounting useful life for technology equipment. This pays a frontier-generation turnover-pressure coordinate. It does not identify retirement cadence, installed fleet shares, impairment, or the economic-obsolescence date of any prior generation."
