module DASHI.Governance.MedicalCannabisPresenceImpairmentBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set)

------------------------------------------------------------------------
-- Presence / prescription / chronic-use / impairment coordinate separation.
--
-- The concrete exposure arithmetic records labelled plant mass and labelled
-- THC fraction only. It is not absorbed dose, blood level, oral-fluid level,
-- impairment, fitness-to-drive advice, or a pharmacokinetic model.

monthlyFlowerGrams : Nat
monthlyFlowerGrams = 120

labelledTHCPercent : Nat
labelledTHCPercent = 30

labelledTHCGramPercentProduct : Nat
labelledTHCGramPercentProduct =
  monthlyFlowerGrams * labelledTHCPercent

labelledTHCGramPercentProductIs3600 :
  labelledTHCGramPercentProduct ≡ 3600
labelledTHCGramPercentProductIs3600 = refl

------------------------------------------------------------------------
-- The legal/scientific coordinates remain distinct types.

record DriverStateCoordinates : Set₁ where
  field
    Prescription : Set
    Presence : Set
    ChronicAdaptation : Set
    FunctionalImpairment : Set
    RegisterStatus : Set
    LicenceClass : Set

record PresenceImpairmentSeparation
  (C : DriverStateCoordinates) : Set₁ where
  field
    presenceCoordinate : DriverStateCoordinates.Presence C
    impairmentCoordinate : DriverStateCoordinates.FunctionalImpairment C

    presenceDeterminesImpairment : Bool
    presenceDeterminesImpairmentIsFalse :
      presenceDeterminesImpairment ≡ false

    prescriptionDeterminesSafety : Bool
    prescriptionDeterminesSafetyIsFalse :
      prescriptionDeterminesSafety ≡ false

open PresenceImpairmentSeparation public

record MedicalCannabisGovernanceBoundary : Set where
  constructor mkMedicalCannabisGovernanceBoundary
  field
    chronicUseTracked : Bool
    chronicUseTrackedIsTrue : chronicUseTracked ≡ true

    presenceImpairmentSeparated : Bool
    presenceImpairmentSeparatedIsTrue :
      presenceImpairmentSeparated ≡ true

    registerAccommodationTracked : Bool
    registerAccommodationTrackedIsTrue :
      registerAccommodationTracked ≡ true

    registerSurveillanceRiskTracked : Bool
    registerSurveillanceRiskTrackedIsTrue :
      registerSurveillanceRiskTracked ≡ true

    absorbedDoseClaimPromoted : Bool
    absorbedDoseClaimPromotedIsFalse : absorbedDoseClaimPromoted ≡ false

    impairmentFindingPromoted : Bool
    impairmentFindingPromotedIsFalse : impairmentFindingPromoted ≡ false

    drivingAdvicePromoted : Bool
    drivingAdvicePromotedIsFalse : drivingAdvicePromoted ≡ false

    reading : String

open MedicalCannabisGovernanceBoundary public

canonicalMedicalCannabisGovernanceBoundary :
  MedicalCannabisGovernanceBoundary
canonicalMedicalCannabisGovernanceBoundary =
  mkMedicalCannabisGovernanceBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Presence, prescription, chronic adaptation, functional impairment, register status, and licence class remain separate coordinates; the concrete 120g at 30 percent label arithmetic is not promoted to absorbed dose or impairment."
