module DASHI.Governance.InstitutionalContinuityRepairArithmetic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact arithmetic and governance boundary for the institutional example.
-- Monetary values are represented in thousands of dollars so the weekly to
-- annual conversion remains finite and exact.  Public figures remain source-
-- bound observations; no legal liability or fraudulent-transfer finding is
-- promoted by this module.

weeklySettlementThousands : Nat
weeklySettlementThousands = 1700

weeksPerYear : Nat
weeksPerYear = 52

annualSettlementThousands : Nat
annualSettlementThousands =
  weeklySettlementThousands * weeksPerYear

annualSettlementIs88400Thousands :
  annualSettlementThousands ≡ 88400
annualSettlementIs88400Thousands = refl

annualRevenueThousands : Nat
annualRevenueThousands = 1277000

allegedRateLowerPercent : Nat
allegedRateLowerPercent = 20

allegedRateUpperPercent : Nat
allegedRateUpperPercent = 22

record InstitutionalContinuityCoordinates : Set where
  constructor mkInstitutionalContinuityCoordinates
  field
    missionContinuity : Bool
    assetContinuityQuestionTracked : Bool
    publicSubsidyContinuity : Bool
    taxPrivilegeContinuity : Bool
    publicLegitimacyContinuity : Bool
    survivorRepairContinuity : Bool

open InstitutionalContinuityCoordinates public

canonicalInstitutionalContinuityCoordinates :
  InstitutionalContinuityCoordinates
canonicalInstitutionalContinuityCoordinates =
  mkInstitutionalContinuityCoordinates
    true true true true true false

record InstitutionalContinuityRepairBoundary : Set where
  constructor mkInstitutionalContinuityRepairBoundary
  field
    coordinates : InstitutionalContinuityCoordinates
    weeklyOutflow : Nat
    annualOutflow : Nat
    annualRevenue : Nat
    lowerAllegedRate : Nat
    upperAllegedRate : Nat

    annualOutflowIsCanonical : annualOutflow ≡ annualSettlementThousands

    assetTransferConcernTracked : Bool
    assetTransferConcernTrackedIsTrue : assetTransferConcernTracked ≡ true

    extendedPeriodTracked : Bool
    extendedPeriodTrackedIsTrue : extendedPeriodTracked ≡ true

    liabilityFindingPromoted : Bool
    liabilityFindingPromotedIsFalse : liabilityFindingPromoted ≡ false

    fraudulentTransferFindingPromoted : Bool
    fraudulentTransferFindingPromotedIsFalse :
      fraudulentTransferFindingPromoted ≡ false

    sourceBoundReading : String

open InstitutionalContinuityRepairBoundary public

canonicalInstitutionalContinuityRepairBoundary :
  InstitutionalContinuityRepairBoundary
canonicalInstitutionalContinuityRepairBoundary =
  mkInstitutionalContinuityRepairBoundary
    canonicalInstitutionalContinuityCoordinates
    weeklySettlementThousands
    annualSettlementThousands
    annualRevenueThousands
    allegedRateLowerPercent
    allegedRateUpperPercent
    refl
    true refl
    true refl
    false refl
    false refl
    "The simultaneous surface is weekly repair pressure, billion-scale annual revenue, high alleged-perpetrator proportion, extended duration, and contested asset-transfer continuity; all remain source-bound and non-adjudicative."
