module DASHI.Law.SensibLawWoogarooScientificEvidenceTypeDiscriminator20261109Exact where

-- Original EPBC 2019/8575 PD v5, 30 Jan 2026 MWW OAMP Tables 12-13,
-- Appendix A and rehabilitation management plan (Saunders Havill).
-- Critiques: Taylor/Maguire/Lewis QUT School of Law 12 Mar 2026;
-- Gough QCC 12 Mar 2026; original RSPCA case-level original reports.
-- Preserves their original authorship and earlier PR #1276 proofs.
--
-- Scientific-EVIDENCE TYPE distinction, not a declaration that an
-- actual future restoration is impossible or an unlawful submission:
-- 20-year expected RE remnant-classification benchmark (>=50% canopy
-- cover and >=70% canopy height under Neldner et al. 2023) is NOT by
-- itself a measured Koala stocking/corridor/thermal-refuge result.
-- Source table cites existence of detailed rehabilitation management
-- plan for 75% confidence in future result; its independent empirical
-- calibration remains a different kind of receipt.
--
-- The January PD's original 2026 source must NOT be treated as the
-- signed 16 Oct approval's explicitly defined July Issue F and
-- 15 October 2026 MWW Issue D plan, unless exact source crosswalk paid.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawWoogarooOperativeInstrumentEvidenceCut20261109Exact as Approval
import DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact as OAG

data ScientificProposition : Set where
  structuralRemnantMappingCriterion : ScientificProposition
  predictedYear20Quality7 : ScientificProposition
  calibratedProbabilityOfAchievingFutureQuality : ScientificProposition
  realisedKoalaOccupancy : ScientificProposition
  realisedLocalMovementAndThermalRefuge : ScientificProposition

data EvidenceKind : Set where
  publishedVegetationBenchmark : EvidenceKind
  authorPreparedRehabilitationPlan : EvidenceKind
  independentEmpiricalRestorationTimeSeries : EvidenceKind
  directEcologicalPopulationAndMovementObservation : EvidenceKind
  exactAcceptedOctoberRevision : EvidenceKind

record SourceSupport : Set where
  constructor source-support
  field
    proposition : ScientificProposition
    evidenceKind : EvidenceKind
    primarySourceDescription : String
    directObservedEcologicalOutcome : Bool
    approvedOctoberVersionConfirmed : Bool
open SourceSupport public

structuralBenchmarksSource : SourceSupport
structuralBenchmarksSource = source-support
  structuralRemnantMappingCriterion publishedVegetationBenchmark
  "MWW January PD OAMP Table 12: proposed year20 regrowth meets remnant mapping at 50% canopy cover/70% canopy height; cites Neldner et al 2023"
  false false

planSupportsForecastAsProponentClaim : SourceSupport
planSupportsForecastAsProponentClaim = source-support
  predictedYear20Quality7 authorPreparedRehabilitationPlan
  "MWW January PD OAMP Tables 12-13 and Appendix A: 3.40 to 6.86 and 3.44 to 6.71 future MHQA; rounded 3 to 7"
  false false

confidenceIsProponentAssertionNotIndependentlyCalibrated : SourceSupport
confidenceIsProponentAssertionNotIndependentlyCalibrated = source-support
  calibratedProbabilityOfAchievingFutureQuality
  authorPreparedRehabilitationPlan
  "MWW Table 12: 75% non-remnant AU future quality confidence; existence of Rehabilitation Management Plan cited as support"
  false false

-- ORIGINAL 2012 OAG how-to, Section 2C: the future quality with
-- offset must at least reach the impact-site quality score, using
-- consistent impact and offset methodology; the original guide
-- explicitly illustrates a *possible* 3 -> 6 improvement (so a
-- universal hard +1 ban cannot be attributed to that 2012 source).
--
-- Source January 2026 PD Part A.i Table A26, impacted habitat overall
-- MHQA 6.78 (rounded OAG 7). MWW January OAMP Table 13 AU1 future
-- 6.86 (rounded 7), AU2 future 6.71 (rounded 7).
-- In source hundredths, AU1 >= impact but AU2 future is 0.07 below
-- impact. Both are 7 under reported integer OAG rounding.
-- This is a SCORING PRECISION / VERSION RECONCILIATION, not evidence
-- of illegal rounding in the approved July/Oct OAG.
originalImpactQualityHundredths : Nat
originalImpactQualityHundredths = 678

mwwAU1FutureQualityHundredths : Nat
mwwAU1FutureQualityHundredths = 686

mwwAU2FutureQualityHundredths : Nat
mwwAU2FutureQualityHundredths = 671

au1FutureAboveImpactByEightHundredths :
  originalImpactQualityHundredths + 8 ≡ mwwAU1FutureQualityHundredths
au1FutureAboveImpactByEightHundredths = refl

au2FutureBelowImpactBySevenHundredths :
  mwwAU2FutureQualityHundredths + 7 ≡ originalImpactQualityHundredths
au2FutureBelowImpactBySevenHundredths = refl

record QualityPrecisionGate : Set where
  constructor quality-precision-gate
  field
    sourceUnroundedAU2BelowImpact : Bool
    publishedOAGBothRounded7 : Bool
    original2012GuideHardOnePointCap : Bool
    approvedOctoberPrecisionRuleObtained : Bool
    legalInvalidityFromThisAloneEstablished : Bool
open QualityPrecisionGate public

januaryQualityPrecision : QualityPrecisionGate
januaryQualityPrecision =
  quality-precision-gate true true false false false

noLegalPromotionFromUnroundedGap :
  legalInvalidityFromThisAloneEstablished januaryQualityPrecision ≡ false
noLegalPromotionFromUnroundedGap = refl

-- The typing distinguishes proponent-assessed predicted vegetation
-- and actual independent population-function observation. It DOES NOT
-- claim that a year20 remnant benchmark can NEVER contribute to Koala
-- habitat: rather that structural equivalence demands additional
-- qualified empirical correspondence.
data Conclusion : Set where
  plausibleVegetationRegrowth realisedSpeciesFunction : Conclusion

data ScientificWeld : EvidenceKind → Conclusion → Set where
  structuralBenchmarkToRegrowth :
    ScientificWeld publishedVegetationBenchmark plausibleVegetationRegrowth
  independentObservedSpeciesUse :
    ScientificWeld directEcologicalPopulationAndMovementObservation
      realisedSpeciesFunction

data OriginalScientificConsumerPaid : Set where
  originalApprovedPlanScientificReview : OriginalScientificConsumerPaid
  independentPopulationEvidence : OriginalScientificConsumerPaid
  originalConfidenceCalibration : OriginalScientificConsumerPaid

-- These booleans are DOCUMENT STAGES, not physical truths.
originalSignedPlanIdentityIsStillOpen :
  Approval.exactDocumentObtained Approval.mountWalkerFinal ≡
    Approval.unknownOriginal
originalSignedPlanIdentityIsStillOpen = refl

originalJanuaryAreaCoefficient :
  OAG.inputSum OAG.mountWalkerRows ≡ 466500
originalJanuaryAreaCoefficient = refl

-- The above is a direct source arithmetic identity for the two
-- 4-point quality-gain MWW AUs (508*4*75+1047*4*75).
-- It verifies numeric dependence, NOT a calibrated forecast.
