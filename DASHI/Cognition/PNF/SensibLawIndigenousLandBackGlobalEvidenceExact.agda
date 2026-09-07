module DASHI.Cognition.PNF.SensibLawIndigenousLandBackGlobalEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Global Indigenous land-back / tenure / authority evidence atlas.
--
-- The atlas is intentionally domain-relative.  It does not compress forest,
-- biodiversity, health, food sovereignty, self-determination and economic
-- outcomes into one scalar.  It also refuses to treat generic private titling
-- as equivalent to Indigenous collective tenure/authority.
------------------------------------------------------------------------

data LandBackEvidenceDomain : Set where
  deforestationDomain : LandBackEvidenceDomain
  forestDegradationDomain : LandBackEvidenceDomain
  secondaryForestRecoveryDomain : LandBackEvidenceDomain
  biodiversityConservationDomain : LandBackEvidenceDomain
  climateResilienceDomain : LandBackEvidenceDomain
  mentalHealthDispossessionDomain : LandBackEvidenceDomain
  foodSovereigntyDomain : LandBackEvidenceDomain
  selfDeterminationWellbeingDomain : LandBackEvidenceDomain
  socioeconomicTradeoffDomain : LandBackEvidenceDomain
  genericPrivateTitlingDomain : LandBackEvidenceDomain


data EvidenceDesign : Set where
  globalSpatialAnalysis : EvidenceDesign
  panTropicalMatchedCounterfactual : EvidenceDesign
  regressionDiscontinuityCausal : EvidenceDesign
  differenceInDifferencesCausal : EvidenceDesign
  systematicReviewDesign : EvidenceDesign
  comparativeObservationalDesign : EvidenceDesign
  officialSynthesisDesign : EvidenceDesign


data EvidenceDirection : Set where
  supportsIndigenousLandAuthority : EvidenceDirection
  dispossessionAssociatedWithHarm : EvidenceDirection
  mixedOrTradeoffEvidence : EvidenceDirection
  counterexampleToGenericTitlingProxy : EvidenceDirection
  descriptiveImportanceOnly : EvidenceDirection


data EvidenceStrength : Set where
  causalLocalStrong : EvidenceStrength
  systematicReviewStrong : EvidenceStrength
  panRegionalComparativeStrong : EvidenceStrength
  globalDescriptiveStrong : EvidenceStrength
  heterogeneousButMaterial : EvidenceStrength
  hypothesisGeneratingOnly : EvidenceStrength


data TenureInterventionKind : Set where
  indigenousCollectiveTenureRecognition : TenureInterventionKind
  fullCollectivePropertyRights : TenureInterventionKind
  indigenousTerritoryGovernance : TenureInterventionKind
  landRestitutionOrReturnIntervention : TenureInterventionKind
  communityFoodSovereigntyIntervention : TenureInterventionKind
  genericPrivateLandTitling : TenureInterventionKind
  dispossessionByIndustrialDevelopment : TenureInterventionKind


record LandBackStudyReceipt : Set where
  constructor landBackStudyReceipt
  field
    studyReference : String
    publicationYear : Nat
    domain : LandBackEvidenceDomain
    design : EvidenceDesign
    direction : EvidenceDirection
    strength : EvidenceStrength
    intervention : TenureInterventionKind
    indigenousCollectiveAuthoritySpecific : Bool
    exactLandBackInterventionStudied : Bool
    exactLandBackInterventionStudiedIsNotAssumed : exactLandBackInterventionStudied ≡ false
    universalOutcomeClaimed : Bool
    universalOutcomeClaimedIsFalse : universalOutcomeClaimed ≡ false
    causalScopeReference : String
open LandBackStudyReceipt public

------------------------------------------------------------------------
-- Environmental / forest evidence.
------------------------------------------------------------------------

garnett2018GlobalIndigenousLands : LandBackStudyReceipt
garnett2018GlobalIndigenousLands = landBackStudyReceipt
  "Garnett et al 2018 Nature Sustainability 1:369-374 doi:10.1038/s41893-018-0100-6"
  2018
  biodiversityConservationDomain
  globalSpatialAnalysis
  descriptiveImportanceOnly
  globalDescriptiveStrong
  indigenousTerritoryGovernance
  true
  false refl
  false refl
  "Indigenous Peoples manage or hold tenure rights over at least about one-quarter of terrestrial surface; lands intersect large shares of protected/intact landscapes; descriptive global importance, not a causal land-return trial"

sze2022PanTropical : LandBackStudyReceipt
sze2022PanTropical = landBackStudyReceipt
  "Sze et al 2022 Nature Sustainability 5:123-130 doi:10.1038/s41893-021-00815-2"
  2022
  deforestationDomain
  panTropicalMatchedCounterfactual
  supportsIndigenousLandAuthority
  panRegionalComparativeStrong
  indigenousTerritoryGovernance
  true
  false refl
  false refl
  "Matched pan-tropical comparison: Indigenous Lands reduced deforestation relative to non-protected areas and broadly performed comparably to protected areas; degradation also reduced"

baragwanathBayi2020 : LandBackStudyReceipt
baragwanathBayi2020 = landBackStudyReceipt
  "Baragwanath & Bayi 2020 PNAS 117:20495-20502 doi:10.1073/pnas.1917874117"
  2020
  deforestationDomain
  regressionDiscontinuityCausal
  supportsIndigenousLandAuthority
  causalLocalStrong
  fullCollectivePropertyRights
  true
  false refl
  false refl
  "Brazilian Amazon: timing of homologation plus border discontinuity used to identify local causal effects; full Indigenous collective property rights significantly reduced deforestation"

baragwanathBayiShinde2023 : LandBackStudyReceipt
baragwanathBayiShinde2023 = landBackStudyReceipt
  "Baragwanath, Bayi & Shinde 2023 PNAS doi:10.1073/pnas.2221346120"
  2023
  secondaryForestRecoveryDomain
  differenceInDifferencesCausal
  supportsIndigenousLandAuthority
  causalLocalStrong
  fullCollectivePropertyRights
  true
  false refl
  false refl
  "Brazilian Amazon: collective property rights in Indigenous territories associated causally with higher secondary forest growth using timing/boundary designs"

------------------------------------------------------------------------
-- Important proxy counterexample: generic titling is not Indigenous land back.
------------------------------------------------------------------------

probst2020PrivateTitlingCounterexample : LandBackStudyReceipt
probst2020PrivateTitlingCounterexample = landBackStudyReceipt
  "Probst et al 2020 Nature Sustainability 3:1019-1026 doi:10.1038/s41893-020-0537-2"
  2020
  genericPrivateTitlingDomain
  comparativeObservationalDesign
  counterexampleToGenericTitlingProxy
  heterogeneousButMaterial
  genericPrivateLandTitling
  false
  false refl
  false refl
  "Brazilian Amazon Terra Legal private titling: small/medium landholders increased deforestation; title issuance alone is not a valid proxy for Indigenous collective tenure/authority"

------------------------------------------------------------------------
-- Health / wellbeing / food sovereignty evidence.
------------------------------------------------------------------------

mortonninomiya2023DispossessionReview : LandBackStudyReceipt
mortonninomiya2023DispossessionReview = landBackStudyReceipt
  "Morton Ninomiya et al 2023 Lancet Planetary Health 7:e501-e517 doi:10.1016/S2542-5196(23)00079-7"
  2023
  mentalHealthDispossessionDomain
  systematicReviewDesign
  dispossessionAssociatedWithHarm
  systematicReviewStrong
  dispossessionByIndustrialDevelopment
  true
  false refl
  false refl
  "Systematic review across Australia, Aotearoa, the Americas and Circumpolar North: land dispossession from industrial development had predominantly negative mental-health impacts and disrupted identity, resources, language, spirituality and ways of life"

indigenousWellbeing2021Review : LandBackStudyReceipt
indigenousWellbeing2021Review = landBackStudyReceipt
  "Systematic review of Indigenous wellbeing in Canada, Aotearoa and the United States, Int J Environ Res Public Health 2021 18:5832"
  2021
  selfDeterminationWellbeingDomain
  systematicReviewDesign
  supportsIndigenousLandAuthority
  systematicReviewStrong
  indigenousTerritoryGovernance
  true
  false refl
  false refl
  "Review identifies self-determination, including collective self-governance, as central to Indigenous wellbeing; not an isolated land-return causal experiment"

foodSovereigntyInterventionReview2023 : LandBackStudyReceipt
foodSovereigntyInterventionReview2023 = landBackStudyReceipt
  "Elements of Successful Food Sovereignty Interventions within Indigenous Communities in US and Canada, Current Developments in Nutrition 2023 7:101973"
  2023
  foodSovereigntyDomain
  systematicReviewDesign
  supportsIndigenousLandAuthority
  systematicReviewStrong
  communityFoodSovereigntyIntervention
  true
  false refl
  false refl
  "Systematic review links colonial land loss to Indigenous food-system disruption and synthesises successful Indigenous food-sovereignty intervention elements"

------------------------------------------------------------------------
-- Socioeconomic trade-off evidence prevents ecological success from being
-- misreported as automatic socioeconomic closure.
------------------------------------------------------------------------

amazonSocioeconomicTradeoff2024 : LandBackStudyReceipt
amazonSocioeconomicTradeoff2024 = landBackStudyReceipt
  "Nature Ecology & Evolution 2024 8:1482-1492, socio-economic and environmental trade-offs in Amazonian protected areas and Indigenous territories"
  2024
  socioeconomicTradeoffDomain
  comparativeObservationalDesign
  mixedOrTradeoffEvidence
  heterogeneousButMaterial
  indigenousTerritoryGovernance
  true
  false refl
  false refl
  "Indigenous territories reduced deforestation by 48-83% relative to competing land uses but showed smaller measured socioeconomic benefits on selected indicators; ecological success does not by itself close socioeconomic justice"

------------------------------------------------------------------------
-- Domain-indexed evidence state.
------------------------------------------------------------------------

data DomainEvidenceState : Set where
  noEvidenceMapped : DomainEvidenceState
  descriptiveSupportMapped : DomainEvidenceState
  strongComparativeSupportMapped : DomainEvidenceState
  strongCausalSupportMapped : DomainEvidenceState
  systematicHarmEvidenceMapped : DomainEvidenceState
  mixedTradeoffMapped : DomainEvidenceState


record GlobalLandBackEvidenceState : Set where
  constructor globalLandBackEvidenceState
  field
    deforestationState : DomainEvidenceState
    biodiversityState : DomainEvidenceState
    restorationState : DomainEvidenceState
    mentalHealthState : DomainEvidenceState
    foodSovereigntyState : DomainEvidenceState
    selfDeterminationState : DomainEvidenceState
    socioeconomicState : DomainEvidenceState
    privateTitlingProxyState : DomainEvidenceState
    stateReference : String
open GlobalLandBackEvidenceState public

currentGlobalEvidenceState : GlobalLandBackEvidenceState
currentGlobalEvidenceState = globalLandBackEvidenceState
  strongCausalSupportMapped
  descriptiveSupportMapped
  strongCausalSupportMapped
  systematicHarmEvidenceMapped
  strongComparativeSupportMapped
  strongComparativeSupportMapped
  mixedTradeoffMapped
  mixedTradeoffMapped
  "Strong domain-relative evidence for Indigenous collective tenure/authority on forests/restoration and strong systematic evidence on dispossession harms/self-determination; socioeconomic outcomes remain heterogeneous and generic private titling is explicitly not treated as LAND BACK"

------------------------------------------------------------------------
-- LAND BACK is represented as a bundle, not as title-paper alone.
------------------------------------------------------------------------

data LandBackComponent : Set where
  territorialReturnOrRestitution : LandBackComponent
  collectiveTenureSecurity : LandBackComponent
  indigenousDecisionAuthority : LandBackComponent
  protectionFromExternalDispossession : LandBackComponent
  culturalAndSpiritualAccess : LandBackComponent
  intergenerationalContinuity : LandBackComponent
  resourceGovernanceAuthority : LandBackComponent
  materialCapacityForStewardship : LandBackComponent


canonicalLandBackBundle : List LandBackComponent
canonicalLandBackBundle =
  territorialReturnOrRestitution
  ∷ collectiveTenureSecurity
  ∷ indigenousDecisionAuthority
  ∷ protectionFromExternalDispossession
  ∷ culturalAndSpiritualAccess
  ∷ intergenerationalContinuity
  ∷ resourceGovernanceAuthority
  ∷ materialCapacityForStewardship
  ∷ []

------------------------------------------------------------------------
-- Evidence-sensitive hypothesis promotion.
------------------------------------------------------------------------

data LandBackHypothesisStatus : Set where
  normativeDemand : LandBackHypothesisStatus
  empiricallySupportedInSomeDomains : LandBackHypothesisStatus
  crossDomainCausalHypothesis : LandBackHypothesisStatus
  universallyProvedOutcome : LandBackHypothesisStatus


record LandBackGlobalHypothesis : Set where
  constructor landBackGlobalHypothesis
  field
    hypothesisReference : String
    status : LandBackHypothesisStatus
    environmentalSupportStrong : Bool
    environmentalSupportStrongIsTrue : environmentalSupportStrong ≡ true
    dispossessionHarmSupportStrong : Bool
    dispossessionHarmSupportStrongIsTrue : dispossessionHarmSupportStrong ≡ true
    everySocioeconomicOutcomeProved : Bool
    everySocioeconomicOutcomeProvedIsFalse : everySocioeconomicOutcomeProved ≡ false
    closingGapCausallySolvedByExistingEvidence : Bool
    closingGapCausallySolvedByExistingEvidenceIsFalse : closingGapCausallySolvedByExistingEvidence ≡ false
open LandBackGlobalHypothesis public

landBackGlobalEvidenceHypothesis : LandBackGlobalHypothesis
landBackGlobalEvidenceHypothesis = landBackGlobalHypothesis
  "Global LAND BACK hypothesis: restoring Indigenous land/tenure/decision authority is strongly supported for multiple ecological and self-determination/health-relevant domains, while exact cross-domain socioeconomic causal magnitude remains open"
  empiricallySupportedInSomeDomains
  true refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- Source hygiene: do not use the widely repeated '80% of biodiversity' claim
-- as a precise empirical premise.  The 2018 global spatial study is used instead.
------------------------------------------------------------------------

record BiodiversityStatisticBoundary : Set where
  constructor mkBiodiversityStatisticBoundary
  field
    eightyPercentClaimUsedAsExactEmpiricalPremise : Bool
    eightyPercentClaimUsedAsExactEmpiricalPremiseIsFalse : eightyPercentClaimUsedAsExactEmpiricalPremise ≡ false
    rigorousGlobalSpatialEvidenceUsedInstead : Bool
    rigorousGlobalSpatialEvidenceUsedInsteadIsTrue : rigorousGlobalSpatialEvidenceUsedInstead ≡ true
open BiodiversityStatisticBoundary public

biodiversityStatisticBoundary : BiodiversityStatisticBoundary
biodiversityStatisticBoundary = mkBiodiversityStatisticBoundary false refl true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data GenericPrivateTitleEqualsLandBack : Set where
data LegalTitleAloneEqualsIndigenousAuthority : Set where
data ForestEvidenceProvesEverySocialOutcome : Set where
data DispossessionHarmProvesExactInverseBenefitMagnitude : Set where
data GlobalDescriptiveOverlapProvesCausalEffect : Set where
data StrongDomainEvidenceMeansUniversalOutcome : Set where
data LandBackEvidenceProvesClosingGapSingleCause : Set where

genericTitleDoesNotEqualLandBack : GenericPrivateTitleEqualsLandBack → ⊥
genericTitleDoesNotEqualLandBack ()
legalTitleAloneDoesNotEqualAuthority : LegalTitleAloneEqualsIndigenousAuthority → ⊥
legalTitleAloneDoesNotEqualAuthority ()
forestEvidenceDoesNotProveEverySocialOutcome : ForestEvidenceProvesEverySocialOutcome → ⊥
forestEvidenceDoesNotProveEverySocialOutcome ()
dispossessionHarmDoesNotFixInverseBenefitMagnitude : DispossessionHarmProvesExactInverseBenefitMagnitude → ⊥
dispossessionHarmDoesNotFixInverseBenefitMagnitude ()
globalOverlapDoesNotByItselfProveCausality : GlobalDescriptiveOverlapProvesCausalEffect → ⊥
globalOverlapDoesNotByItselfProveCausality ()
strongDomainEvidenceDoesNotMeanUniversalOutcome : StrongDomainEvidenceMeansUniversalOutcome → ⊥
strongDomainEvidenceDoesNotMeanUniversalOutcome ()
landBackEvidenceDoesNotProveSingleClosingGapCause : LandBackEvidenceProvesClosingGapSingleCause → ⊥
landBackEvidenceDoesNotProveSingleClosingGapCause ()
