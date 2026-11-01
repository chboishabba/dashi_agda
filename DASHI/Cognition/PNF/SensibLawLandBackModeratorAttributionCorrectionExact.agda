module DASHI.Cognition.PNF.SensibLawLandBackModeratorAttributionCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSocioeconomicModeratorHyperfabricExact as Historical
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source

------------------------------------------------------------------------
-- Additive correction for a historical local label.
--
-- `officialAssociationMapped` was too strong because CPI/PUC-Rio authored the
-- analysis. Official Brazilian datasets are inputs; they do not make the CPI
-- analytical proposition an official-government proposition.
------------------------------------------------------------------------

data PreferredModeratorEvidenceStatus : Set where
  independentPolicyAssociationMapped : PreferredModeratorEvidenceStatus
  historicalPeerReviewedMechanismMapped : PreferredModeratorEvidenceStatus
  institutionalEconomicValuationMapped : PreferredModeratorEvidenceStatus
  sourceSuggestedMechanismMapped : PreferredModeratorEvidenceStatus
  criticalModeratorHypothesisOnly : PreferredModeratorEvidenceStatus


record ModeratorAttributionCorrection : Set where
  constructor moderatorAttributionCorrection
  field
    historicalReceipt : Historical.SocioeconomicModeratorReceipt
    historicalStatus : Historical.ModeratorEvidenceStatus
    preferredStatus : PreferredModeratorEvidenceStatus
    sourceAuthority : Source.SourceAuthorityReceipt
    correctionRequired : Bool
    correctionRequiredIsTrue : correctionRequired ≡ true
    historicalReceiptDeleted : Bool
    historicalReceiptDeletedIsFalse : historicalReceiptDeleted ≡ false
    correctionReference : String
open ModeratorAttributionCorrection public

cpiModeratorAttributionCorrection : ModeratorAttributionCorrection
cpiModeratorAttributionCorrection = moderatorAttributionCorrection
  Historical.cpiCreditDistortionReceipt
  Historical.officialAssociationMapped
  independentPolicyAssociationMapped
  Source.cpi2024RuralCreditAuthority
  true refl
  false refl
  "CPI/PUC-Rio 2024 is independent policy research using official Brazilian datasets. Downstream use must attribute the reported subsidized-credit/deforestation association to CPI/PUC-Rio, not to the Brazilian government."

historicalCpiStatusRecorded :
  Historical.status Historical.cpiCreditDistortionReceipt ≡ Historical.officialAssociationMapped
historicalCpiStatusRecorded = refl

preferredCpiStatusIsIndependent :
  preferredStatus cpiModeratorAttributionCorrection ≡ independentPolicyAssociationMapped
preferredCpiStatusIsIndependent = refl

cpiSourceAuthorityIsIndependentPolicyResearch :
  Source.authorityKind (sourceAuthority cpiModeratorAttributionCorrection)
  ≡ Source.independentPolicyResearch
cpiSourceAuthorityIsIndependentPolicyResearch = refl

cpiUsesOfficialData :
  Source.usesOfficialUnderlyingData (sourceAuthority cpiModeratorAttributionCorrection) ≡ true
cpiUsesOfficialData = refl

cpiAnalysisNotGovernmentAuthored :
  Source.analysisAuthorIsGovernment (sourceAuthority cpiModeratorAttributionCorrection) ≡ false
cpiAnalysisNotGovernmentAuthored = refl

------------------------------------------------------------------------
-- No-transfer laws.
------------------------------------------------------------------------

data OfficialDatasetTransfersAnalyticalAuthorship : Set where
data HistoricalLocalLabelDeterminesPreferredAttribution : Set where

officialDatasetDoesNotTransferAuthorship : OfficialDatasetTransfersAnalyticalAuthorship → ⊥
officialDatasetDoesNotTransferAuthorship ()
historicalLabelDoesNotFixPreferredAttribution : HistoricalLocalLabelDeterminesPreferredAttribution → ⊥
historicalLabelDoesNotFixPreferredAttribution ()
