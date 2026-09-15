module DASHI.Wikimedia.IbrahimCannabisFadedFarmingPesticideOccurrenceParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisFadedFarmingRegulatoryClaimCrossPollinationExact as Faded
import DASHI.Wikimedia.IbrahimCannabisContaminantToxicantAssayParetoExact as Contaminant
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- INDEPENDENT PESTICIDE OCCURRENCE PAYMENT FOR THE FADEDFARMING LANE
--
-- This owner asks a narrower question than toxicology: do independently
-- measured cannabis samples actually contain chemicals overlapping the named
-- social/regulatory concern set?  Gagnon et al. 2023 supplies a 327-analyte
-- validated multiresidue study across licensed and illicit Canadian flower.
------------------------------------------------------------------------

record OccurrenceSource : Set where
  constructor occurrence-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    directLink : String
    sourceRole : String
    boundedReading : String
    excludedPromotion : String
open OccurrenceSource public

gagnon2023 : OccurrenceSource
gagnon2023 = occurrence-source
  "Mathieu Gagnon; Tyler McRitchie; Kim Montsion; Josee Tully; Michel Blais; Neil Snider; David R. Blais"
  "High levels of pesticides found in illicit cannabis inflorescence compared to licensed samples in Canadian study using expanded 327 pesticides multiresidue method"
  "Journal of Cannabis Research 5:34"
  2023
  "10.1186/s42238-023-00200-0"
  "https://doi.org/10.1186/s42238-023-00200-0"
  "Health Canada laboratory primary multiresidue occurrence study"
  "36 licensed retail samples and 24 illicit law-enforcement seizure samples from 2021 were analysed by modified QuEChERS with GC-MS/MS and LC-MS/MS for 327 pesticide active ingredients."
  "Occurrence and concentration do not by themselves establish route-specific toxic dose, clinical harm, or prevalence outside this sampled panel."

record PanelMethodReceipt : Set where
  constructor panel-method-receipt
  field
    licensedSampleCount : Nat
    illicitSampleCount : Nat
    analyteCount : Nat
    licensedSamplingReference : String
    illicitSamplingReference : String
    preparationReference : String
    platformsReference : String
    lowestCalibratedLevelReference : String
    methodValidated : Bool
open PanelMethodReceipt public

gagnonMethod : PanelMethodReceipt
gagnonMethod = panel-method-receipt
  36 24 327
  "licensed samples purchased in 2021 from Ontario Cannabis Store, spanning licence holders in five Canadian regions"
  "illicit samples obtained from law-enforcement seizures across Canada and submitted to Health Canada"
  "modified QuEChERS multiresidue preparation"
  "GC-MS/MS plus LC-MS/MS"
  "method lowest calibrated level 0.01 microgram/g for the headline licensed detections; analyte-specific validation retained in source/supplement"
  true

------------------------------------------------------------------------
-- Cohort-level result.
------------------------------------------------------------------------

record CohortOccurrenceReceipt : Set where
  constructor cohort-occurrence-receipt
  field
    cohort : String
    sampleCount : Nat
    positiveRateReference : String
    uniquePesticideReference : String
    averagePesticidesPerPositiveOrSampleReference : String
    sourcePaid : Bool
open CohortOccurrenceReceipt public

licensedCohort : CohortOccurrenceReceipt
licensedCohort = cohort-occurrence-receipt
  "Canadian licensed cannabis inflorescence"
  36
  "6% sample positivity rate"
  "two residues quantified: dichlobenil and myclobutanil, each at 0.01 microgram/g in one sample"
  "not promoted beyond source-reported panel"
  true

illicitCohort : CohortOccurrenceReceipt
illicitCohort = cohort-occurrence-receipt
  "Canadian illicit cannabis inflorescence"
  24
  "92% sample positivity rate"
  "23 unique pesticide active ingredients"
  "3.7 different pesticides identified on average per sample"
  true

------------------------------------------------------------------------
-- Exact overlaps with chemicals already surfaced in the attached
-- @fadedfarming discovery summary.
------------------------------------------------------------------------

record SocialOverlapOccurrence : Set where
  constructor social-overlap-occurrence
  field
    chemicalLabel : String
    pubChemCID : String
    sourceCohort : String
    positiveSampleCount : Nat
    concentrationRangeUgPerG : String
    sourceReference : String
    socialClaimExactTranscriptPaid : Bool
    empiricalOccurrencePaid : Bool
    toxicExposurePaid : Bool
open SocialOverlapOccurrence public

imidaclopridOccurrence : SocialOverlapOccurrence
imidaclopridOccurrence = social-overlap-occurrence
  "imidacloprid"
  "86287518"
  "illicit Canadian cannabis inflorescence panel"
  3
  "0.1 to 60 microgram/g"
  "Gagnon et al. 2023 Table 3"
  false true false

paclobutrazolOccurrence : SocialOverlapOccurrence
paclobutrazolOccurrence = social-overlap-occurrence
  "paclobutrazol"
  "73671"
  "illicit Canadian cannabis inflorescence panel"
  10
  "0.009 to 1 microgram/g"
  "Gagnon et al. 2023 Table 3"
  false true false

abamectinOccurrence : SocialOverlapOccurrence
abamectinOccurrence = social-overlap-occurrence
  "abamectin"
  "9920327"
  "illicit Canadian cannabis inflorescence panel"
  2
  "0.06 to 0.6 microgram/g"
  "Gagnon et al. 2023 Table 3"
  false true false

------------------------------------------------------------------------
-- Useful adjacent discriminator: myclobutanil is not one of the exact named
-- social chemicals formalised above, but it is a strong cannabis-pesticide
-- occurrence coordinate and appears in both licensed and illicit cohorts.
------------------------------------------------------------------------

record AdjacentOccurrence : Set where
  constructor adjacent-occurrence
  field
    chemicalLabel : String
    licensedReference : String
    illicitReference : String
    directSocialOverlapPaid : Bool
open AdjacentOccurrence public

myclobutanilOccurrence : AdjacentOccurrence
myclobutanilOccurrence = adjacent-occurrence
  "myclobutanil"
  "one licensed sample at 0.01 microgram/g"
  "17 illicit samples, 0.02 to 70 microgram/g"
  false

------------------------------------------------------------------------
-- What this pays and what it does not.
------------------------------------------------------------------------

data NamedChemicalConcernCreatesPrevalence : Set where
data IllicitOccurrenceCreatesLicensedOccurrence : Set where
data OccurrenceCreatesToxicDose : Set where
data CanadianPanelCreatesGlobalPrevalence : Set where

namedConcernDoesNotCreatePrevalence : NamedChemicalConcernCreatesPrevalence → ⊥
namedConcernDoesNotCreatePrevalence ()

illicitOccurrenceDoesNotCreateLicensedOccurrence : IllicitOccurrenceCreatesLicensedOccurrence → ⊥
illicitOccurrenceDoesNotCreateLicensedOccurrence ()

occurrenceDoesNotCreateToxicDose : OccurrenceCreatesToxicDose → ⊥
occurrenceDoesNotCreateToxicDose ()

canadianPanelDoesNotCreateGlobalPrevalence : CanadianPanelCreatesGlobalPrevalence → ⊥
canadianPanelDoesNotCreateGlobalPrevalence ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data OccurrenceParetoTarget : Set where
  exactSocialTranscript
  productLabelLegality
  licensedMarketReplication
  analyteTransferUnderSmoking
  analyteTransferUnderVaporisation
  inhalationToxicology
  globalPrevalenceClaim : OccurrenceParetoTarget

record OccurrenceParetoStep : Set where
  constructor occurrence-pareto-step
  field
    priority : Nat
    target : OccurrenceParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open OccurrenceParetoStep public

pareto0 : OccurrenceParetoStep
pareto0 = occurrence-pareto-step
  0 exactSocialTranscript
  "recover exact Dc9ru24vk-S transcript and any reel-specific named chemical propositions"
  "precise social claim object"
  "none"

pareto1 : OccurrenceParetoStep
pareto1 = occurrence-pareto-step
  1 productLabelLegality
  "complete exact Admire Pro and Previcur Flex cannabis-use legality joins in the relevant jurisdiction(s)"
  "legal-use discriminator distinct from toxicity"
  "exact product/jurisdiction required"

pareto2 : OccurrenceParetoStep
pareto2 = occurrence-pareto-step
  2 licensedMarketReplication
  "seek independent broad-panel studies in regulated licensed cannabis markets that include imidacloprid, paclobutrazol and abamectin"
  "tests whether the illicit-panel signal generalises to regulated retail"
  "do not infer from illicit samples"

pareto3 : OccurrenceParetoStep
pareto3 = occurrence-pareto-step
  3 analyteTransferUnderSmoking
  "recover analyte-specific mainstream-smoke transfer/degradation measurements from known starting residues"
  "smoked-route dose transform"
  "occurrence concentration required"

pareto4 : OccurrenceParetoStep
pareto4 = occurrence-pareto-step
  4 analyteTransferUnderVaporisation
  "recover analyte-specific aerosol transfer/degradation measurements under defined vaporisation conditions"
  "vaporised-route dose transform"
  "do not copy combustion results into vaporisation"

pareto5 : OccurrenceParetoStep
pareto5 = occurrence-pareto-step
  5 inhalationToxicology
  "compare route-specific transferred dose against analyte-specific inhalation evidence"
  "hazard conclusion"
  "dominated by transfer and dose"

pareto99 : OccurrenceParetoStep
pareto99 = occurrence-pareto-step
  99 globalPrevalenceClaim
  "do not call these chemicals the most common cannabis poisons globally from one Canadian licensed/illicit comparison"
  "nothing without broader representative evidence"
  "dominated by replication"

------------------------------------------------------------------------
-- Temporal evidence.
------------------------------------------------------------------------

data OccurrenceTime : Set where
  source2023
  attachedSocialSnapshot2026
  currentDashi : OccurrenceTime

data OccurrenceInterpretation : Set where
  namedChemicalsOccurInSomeCannabis
  illicitPanelHigherPositiveRate
  licensedMarketGenerallyContainsNamedChemicals
  occurrenceEqualsPoisoning : OccurrenceInterpretation

data OccurrenceSummary : Set where occurrenceIsSampleAndCohortIndexed : OccurrenceSummary

OccurrenceCompatible : OccurrenceTime → OccurrenceInterpretation → Set
OccurrenceCompatible source2023 namedChemicalsOccurInSomeCannabis = ⊤
OccurrenceCompatible source2023 illicitPanelHigherPositiveRate = ⊤
OccurrenceCompatible source2023 licensedMarketGenerallyContainsNamedChemicals = ⊥
OccurrenceCompatible source2023 occurrenceEqualsPoisoning = ⊥
OccurrenceCompatible attachedSocialSnapshot2026 namedChemicalsOccurInSomeCannabis = ⊤
OccurrenceCompatible attachedSocialSnapshot2026 illicitPanelHigherPositiveRate = ⊤
OccurrenceCompatible attachedSocialSnapshot2026 licensedMarketGenerallyContainsNamedChemicals = ⊥
OccurrenceCompatible attachedSocialSnapshot2026 occurrenceEqualsPoisoning = ⊥
OccurrenceCompatible currentDashi namedChemicalsOccurInSomeCannabis = ⊤
OccurrenceCompatible currentDashi illicitPanelHigherPositiveRate = ⊤
OccurrenceCompatible currentDashi licensedMarketGenerallyContainsNamedChemicals = ⊥
OccurrenceCompatible currentDashi occurrenceEqualsPoisoning = ⊥

occurrenceTemporalSystem : Temporal.TemporalEvidenceSystem
occurrenceTemporalSystem = record
  { Time = OccurrenceTime
  ; Interpretation = OccurrenceInterpretation
  ; Compatible = OccurrenceCompatible
  ; Summary = OccurrenceSummary
  ; summarize = λ _ → occurrenceIsSampleAndCohortIndexed
  ; timeReference = λ
      { source2023 → "Gagnon et al. 2023 DOI 10.1186/s42238-023-00200-0"
      ; attachedSocialSnapshot2026 → "user-attached @fadedfarming discovery snapshot, September 2026"
      ; currentDashi → "current DASHI pesticide occurrence/social cross-pollination frontier"
      }
  }

currentOccurrenceFibre : Temporal.EvidenceFibre occurrenceTemporalSystem currentDashi
currentOccurrenceFibre = Temporal.liveInterpretationAt namedChemicalsOccurInSomeCannabis tt

record PesticideOccurrenceBoundary : Set where
  constructor pesticide-occurrence-boundary
  field
    independentOccurrencePaid : Bool
    namedSocialChemicalOverlapPaid : Bool
    illicitDoesNotGeneraliseToLicensed : Bool
    occurrenceDoesNotEqualToxicity : Bool
    routeSpecificTransferStillRequired : Bool
open PesticideOccurrenceBoundary public

canonicalPesticideOccurrenceBoundary : PesticideOccurrenceBoundary
canonicalPesticideOccurrenceBoundary =
  pesticide-occurrence-boundary true true true true true
