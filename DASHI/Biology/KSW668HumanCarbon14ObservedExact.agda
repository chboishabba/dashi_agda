module DASHI.Biology.KSW668HumanCarbon14ObservedExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- E1: PRIMARY ORIGINAL HUMAN AMS MEASUREMENTS (NOT a synthetic example).
-- Heinemeier et al. FASEB Journal 27, 2074–2079 (2013)
-- DOI 10.1096/fj.12-225599, Table 1.
--
-- Same donor, different tissues measured at the original 2000 autopsy.
-- 34 reported assay rows, 30 tendon + 4 muscle, 28 donors; original
-- source marks donors 25, 28, 30 as atmospheric-reference outliers.
-- Source measurements are in pMC * 100, NOT automatically F14C * 100.
-- No isotope nuclear production or emotion intervention was measured.
------------------------------------------------------------------------

data Tissue : Set where
  tendonCore musclePsoas : Tissue

record PrimaryAMSObservation : Set where
  constructor primary-ams
  field
    donorRef : String
    originalAMSId : String
    sample : Tissue
    birthYear : Nat
    pMCHundredths : Nat
    sigmaPMCHundredths : Nat
    originPaperDOI : String
    sourceCalibrationYear : String

open PrimaryAMSObservation public

donor24Tendon : PrimaryAMSObservation
donor24Tendon = primary-ams
  "24" "16243" tendonCore 1947 13571 35
  "10.1096/fj.12-225599" "1962/1976"

donor24Muscle : PrimaryAMSObservation
donor24Muscle = primary-ams
  "24" "17279" musclePsoas 1947 10996 34
  "10.1096/fj.12-225599" "1957/1998"

donor26Tendon : PrimaryAMSObservation
donor26Tendon = primary-ams
  "26" "16246" tendonCore 1958 14848 41
  "10.1096/fj.12-225599" "1962/1972"

donor26Muscle : PrimaryAMSObservation
donor26Muscle = primary-ams
  "26" "17281" musclePsoas 1958 10979 34
  "10.1096/fj.12-225599" "1998"

donor24SameOriginalBirthYear :
  birthYear donor24Tendon ≡ birthYear donor24Muscle
donor24SameOriginalBirthYear = refl

donor26SameOriginalBirthYear :
  birthYear donor26Tendon ≡ birthYear donor26Muscle
donor26SameOriginalBirthYear = refl

donor24MeasuredDifferentTissue14C :
  pMCHundredths donor24Tendon
  ≡ pMCHundredths donor24Muscle + 2575
donor24MeasuredDifferentTissue14C = refl

donor26MeasuredDifferentTissue14C :
  pMCHundredths donor26Tendon
  ≡ pMCHundredths donor26Muscle + 3869
donor26MeasuredDifferentTissue14C = refl

------------------------------------------------------------------------
-- Attribution and scope:
-- measured pMC differences between tissue classes are compatible with
-- environmental uptake/turnover; they are not matched longitudinal
-- measurements or a nuclear transmutation intervention.
------------------------------------------------------------------------
