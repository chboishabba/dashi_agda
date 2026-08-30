module DASHI.Chemistry.DrinkingWaterChloramineNitrificationBiofilmBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.DrinkingWaterChloramineDBPBoundaryExact as Combined
import DASHI.Chemistry.DrinkingWaterDistributionResidualCorrosionBidiExact as Distribution
import DASHI.Chemistry.TransitionKernel as Chemistry

------------------------------------------------------------------------
-- CHLORAMINE DISTRIBUTION: NITRIFICATION / BIOFILM BIDI
--
-- Source anchor: WHO Water Safety in Distribution. In chloraminated systems,
-- nitrification is associated with ammonia oxidation to nitrite/nitrate and can
-- coincide with chloramine residual loss, biofilm growth and changes in pH,
-- alkalinity and dissolved oxygen. Excess free ammonia, warm conditions and
-- low residual can promote risk, but none is individually diagnostic.
------------------------------------------------------------------------

data NitrificationEvidenceKind : Set where
  ammoniaShift
  nitriteShift
  nitrateShift
  residualLoss
  pHShift
  alkalinityShift
  dissolvedOxygenShift
  microbiologicalEvidence
  : NitrificationEvidenceKind

record NitrificationStateReceipt : Set₁ where
  constructor nitrificationStateReceipt
  field
    combinedChlorineState : Combined.CombinedChlorineResidualState
    hydraulicState : Distribution.DistributionHydraulicState
    freeAmmoniaReference : String
    ammoniumReference : String
    nitriteReference : String
    nitrateReference : String
    pHReference : String
    alkalinityReference : String
    dissolvedOxygenReference : String
    temperatureReference : String
    nitrifierEvidenceReference : String
    chloramineResidualReference : String
    validationReference : String

open NitrificationStateReceipt public

record DistributionBiofilmReceipt : Set₁ where
  constructor distributionBiofilmReceipt
  field
    waterChemistry : Chemistry.ReactionNetwork
    hydraulicState : Distribution.DistributionHydraulicState
    pipeMaterialReference : String
    nutrientReference : String
    attachedBiomassReference : String
    microbialCommunityReference : String
    disinfectantPenetrationReference : String
    detachmentReference : String
    regrowthReference : String
    samplingMethodReference : String
    validationReference : String

open DistributionBiofilmReceipt public

record ChloramineNitrificationBiofilmWeld : Set₁ where
  constructor chloramineNitrificationBiofilmWeld
  field
    nitrification : NitrificationStateReceipt
    biofilm : DistributionBiofilmReceipt
    commonHydraulicState :
      hydraulicState nitrification ≡ DistributionBiofilmReceipt.hydraulicState biofilm
    residualBiofilmCouplingReference : String
    ammoniaNitrificationCouplingReference : String
    pHAlkalinityCouplingReference : String
    nitrificationBiofilmCouplingReference : String
    interventionValidationReference : String

open ChloramineNitrificationBiofilmWeld public

record ChloramineNitrificationBiofilmBoundary : Set where
  constructor chloramineNitrificationBiofilmBoundary
  field
    lowChloramineResidualProvesNitrification : Bool
    lowChloramineResidualProvesNitrificationIsFalse :
      lowChloramineResidualProvesNitrification ≡ false

    nitriteDetectionProvesUniqueNitrificationMechanism : Bool
    nitriteDetectionProvesUniqueNitrificationMechanismIsFalse :
      nitriteDetectionProvesUniqueNitrificationMechanism ≡ false

    biofilmPresenceProvesPathogenPresence : Bool
    biofilmPresenceProvesPathogenPresenceIsFalse :
      biofilmPresenceProvesPathogenPresence ≡ false

    chloraminePersistenceProvesBiofilmEradication : Bool
    chloraminePersistenceProvesBiofilmEradicationIsFalse :
      chloraminePersistenceProvesBiofilmEradication ≡ false

    nitrificationStateRecoversUniqueTreatmentHistory : Bool
    nitrificationStateRecoversUniqueTreatmentHistoryIsFalse :
      nitrificationStateRecoversUniqueTreatmentHistory ≡ false

    nitrificationAssessmentNeedsChemicalMicrobialAndHydraulicReceipts : Bool
    nitrificationAssessmentNeedsChemicalMicrobialAndHydraulicReceiptsIsTrue :
      nitrificationAssessmentNeedsChemicalMicrobialAndHydraulicReceipts ≡ true

canonicalChloramineNitrificationBiofilmBoundary : ChloramineNitrificationBiofilmBoundary
canonicalChloramineNitrificationBiofilmBoundary =
  chloramineNitrificationBiofilmBoundary
    false refl false refl false refl false refl false refl true refl
