module DASHI.Education.RoseContextLearningSourceBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BOUNDED "SMELL THE ROSES" CROSS-POLLINATION
--
-- Keisuke Kokubun, Kiyotaka Nemoto, Yoshinori Yamakawa,
-- "Continuous inhalation of essential oil increases gray matter volume",
-- Brain Research Bulletin 208 (2024), 110896.
-- DOI: 10.1016/j.brainresbull.2024.110896.
--
-- The study motivates treating olfactory exposure as one contextual/sensory
-- input channel.  This module deliberately does not promote one small MRI
-- intervention into a universal learning, therapeutic, causal-mechanism or
-- dementia-prevention theorem.
------------------------------------------------------------------------

roseStudyTitle : String
roseStudyTitle = "Continuous inhalation of essential oil increases gray matter volume"

roseStudyAuthors : String
roseStudyAuthors = "Keisuke Kokubun; Kiyotaka Nemoto; Yoshinori Yamakawa"

roseStudyDOI : String
roseStudyDOI = "10.1016/j.brainresbull.2024.110896"

record RoseContextEvidenceBoundary : Set where
  constructor roseContextEvidenceBoundary
  field
    title authors doi : String
    olfactoryExposureIsAdmissibleContextChannel : Bool
    structuralMRIObservationRetained : Bool
    exposureAloneProvesUniversalLearningBenefit : Bool
    exposureAloneProvesUniversalLearningBenefitIsFalse :
      exposureAloneProvesUniversalLearningBenefit ≡ false
    exposureAloneProvesTherapeuticBenefit : Bool
    exposureAloneProvesTherapeuticBenefitIsFalse :
      exposureAloneProvesTherapeuticBenefit ≡ false
    exposureAloneProvesCellularMechanism : Bool
    exposureAloneProvesCellularMechanismIsFalse :
      exposureAloneProvesCellularMechanism ≡ false
    exposureAloneProvesDementiaPrevention : Bool
    exposureAloneProvesDementiaPreventionIsFalse :
      exposureAloneProvesDementiaPrevention ≡ false

open RoseContextEvidenceBoundary public

canonicalRoseContextEvidenceBoundary : RoseContextEvidenceBoundary
canonicalRoseContextEvidenceBoundary =
  roseContextEvidenceBoundary
    roseStudyTitle
    roseStudyAuthors
    roseStudyDOI
    true
    true
    false refl
    false refl
    false refl
    false refl
