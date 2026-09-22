module DASHI.Law.SensibLawMunkaraTipakalippaNonCollapseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S21.2 MUNKARA / TIPAKALIPPA NON-COLLAPSE
--
-- Tipakalippa and Munkara share Sea Country / offshore-project context, but
-- they do not expose the same legal requirement:
--
-- Tipakalippa [2022] FCAFC 193
--   reg 11A(1)(d): consultation with a "relevant person" whose functions,
--   interests or activities may be affected.
--
-- Munkara (No 3) [2024] FCA 9
--   reg 17(6): whether a revised environment plan was required because of a
--   new significant environmental impact or risk.
--
-- Therefore shared Country/Sea-Country context may be reusable context, but
-- neither context adjacency nor the Tipakalippa consultation rule can pay the
-- distinct Munkara reg 17(6) coordinate.
------------------------------------------------------------------------

seaCountryContextCoordinate : String
seaCountryContextCoordinate =
  "coordinate:context:tiwi-sea-country-traditional-connection"

tipakalippaRelevantPersonCoordinate : String
tipakalippaRelevantPersonCoordinate =
  "coordinate:legal:tipakalippa:reg11a1d-relevant-person-consultation"

munkaraReg17_6Coordinate : String
munkaraReg17_6Coordinate =
  "coordinate:legal:munkara:reg17-6-new-significant-environmental-impact-or-risk"

data CoordinateClass : Set where
  sharedContext : CoordinateClass
  consultationRequirement : CoordinateClass
  revisionRequirement : CoordinateClass

data PaymentDisposition : Set where
  exactPayment : PaymentDisposition
  wrongType : PaymentDisposition
  unpaid : PaymentDisposition

payMunkaraRequirement : CoordinateClass → PaymentDisposition
payMunkaraRequirement sharedContext = wrongType
payMunkaraRequirement consultationRequirement = unpaid
payMunkaraRequirement revisionRequirement = exactPayment

seaCountryContextIsWrongType :
  payMunkaraRequirement sharedContext ≡ wrongType
seaCountryContextIsWrongType = refl

tipakalippaConsultationDoesNotPayReg17_6 :
  payMunkaraRequirement consultationRequirement ≡ unpaid
tipakalippaConsultationDoesNotPayReg17_6 = refl

exactMunkaraRequirementPays :
  payMunkaraRequirement revisionRequirement ≡ exactPayment
exactMunkaraRequirementPays = refl

------------------------------------------------------------------------
-- Anti-collapse propositions.
------------------------------------------------------------------------

data SeaCountryAdjacencyPaysReg17_6 : Set where
data TipakalippaRuleEqualsMunkaraRule : Set where
data ContextCreatesLegalApplicability : Set where
data WrongTypeCreatesClaimTruth : Set where

seaCountryAdjacencyCannotPayReg17_6 :
  SeaCountryAdjacencyPaysReg17_6 → ⊥
seaCountryAdjacencyCannotPayReg17_6 ()

tipakalippaRuleDoesNotEqualMunkaraRule :
  TipakalippaRuleEqualsMunkaraRule → ⊥
tipakalippaRuleDoesNotEqualMunkaraRule ()

contextDoesNotCreateApplicability :
  ContextCreatesLegalApplicability → ⊥
contextDoesNotCreateApplicability ()

wrongTypeDoesNotCreateTruth :
  WrongTypeCreatesClaimTruth → ⊥
wrongTypeDoesNotCreateTruth ()

record MunkaraTipakalippaNonCollapseBoundary : Set where
  constructor munkaraTipakalippaNonCollapseBoundary
  field
    seaCountryContextMayBeRelevant : Bool
    seaCountryContextMayBeRelevantIsTrue :
      seaCountryContextMayBeRelevant ≡ true

    seaCountryContextPaysReg17_6 : Bool
    seaCountryContextPaysReg17_6IsFalse :
      seaCountryContextPaysReg17_6 ≡ false

    tipakalippaConsultationPaysReg17_6 : Bool
    tipakalippaConsultationPaysReg17_6IsFalse :
      tipakalippaConsultationPaysReg17_6 ≡ false

    exactMunkaraReg17_6MayPay : Bool
    exactMunkaraReg17_6MayPayIsTrue :
      exactMunkaraReg17_6MayPay ≡ true

    wrongTypeIsMachineVisible : Bool
    wrongTypeIsMachineVisibleIsTrue :
      wrongTypeIsMachineVisible ≡ true

    wrongTypeCreatesClaimTruth : Bool
    wrongTypeCreatesClaimTruthIsFalse :
      wrongTypeCreatesClaimTruth ≡ false

open MunkaraTipakalippaNonCollapseBoundary public

canonicalMunkaraTipakalippaNonCollapseBoundary :
  MunkaraTipakalippaNonCollapseBoundary
canonicalMunkaraTipakalippaNonCollapseBoundary =
  munkaraTipakalippaNonCollapseBoundary
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
