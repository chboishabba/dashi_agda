{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.Round13ClosureBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Standalone status boundary transcribed from the existing R191/R193 owners.
-- It does not import unsafe modules or prove their analytic obligations.
record ClosureBoundary : Set where
  constructor closureBoundary
  field
    productionEnergyLedgerClosed : Bool
    externalSignedCellExpansionClosed : Bool
    selfOwnerPaymentClosed : Bool
    externalTrajectoryPaymentClosed : Bool
    packageAClosed : Bool
    clayPromoted : Bool

round13Boundary : ClosureBoundary
round13Boundary = closureBoundary true true false false false false

energyLedgerStatus :
  ClosureBoundary.productionEnergyLedgerClosed round13Boundary ≡ true
energyLedgerStatus = refl

externalCellsStatus :
  ClosureBoundary.externalSignedCellExpansionClosed round13Boundary ≡ true
externalCellsStatus = refl

selfOwnerPaymentStillOpen :
  ClosureBoundary.selfOwnerPaymentClosed round13Boundary ≡ false
selfOwnerPaymentStillOpen = refl

externalTrajectoryPaymentStillOpen :
  ClosureBoundary.externalTrajectoryPaymentClosed round13Boundary ≡ false
externalTrajectoryPaymentStillOpen = refl

packageAStillOpen :
  ClosureBoundary.packageAClosed round13Boundary ≡ false
packageAStillOpen = refl

noClayPromotion :
  ClosureBoundary.clayPromoted round13Boundary ≡ false
noClayPromotion = refl
