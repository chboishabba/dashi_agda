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
