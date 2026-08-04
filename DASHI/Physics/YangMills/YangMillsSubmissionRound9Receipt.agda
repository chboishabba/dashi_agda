module DASHI.Physics.YangMills.YangMillsSubmissionRound9Receipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.YangMillsSubmissionRound9Ledger as Ledger

record Round9Receipt : Set where
  field
    trancheName : String
    physicalInvolutionOwned :
      Ledger.physicalInvolutionCoreOwned ≡ true
    centeredParityOwned :
      Ledger.centeredCMP109CoordinateInvolutionOwned ≡ true
    contourInverseOwned :
      Ledger.noncommutativeContourInverseOwned ≡ true
    concretePeriodicDegreeOwned :
      Ledger.periodicConcreteDegreeEightOwned ≡ true
    siDimensionBridgeOwned :
      Ledger.siMechanicalDimensionBridgeOwned ≡ true

    factorialCoefficientLeafStillOpen :
      Ledger.bishopConcreteFactorialDenominatorBoundOwned ≡ false
    physicalP06LeafStillOpen :
      Ledger.p06PhysicalModelLeafOwned ≡ false
    physicalP10StillOpen :
      Ledger.p10PhysicalSuppressionOwned ≡ false
    physicalP33StillOpen :
      Ledger.p33PhysicalEllipticityOwned ≡ false
    terminalSubmissionStillOpen :
      Ledger.fullYangMillsSubmissionComplete ≡ false

open Round9Receipt public

round9Receipt : Round9Receipt
round9Receipt = record
  { trancheName =
      "Yang--Mills round nine: physical involutions, Bishop parity, contour inversion, P06/P11/P10/P33 cutsets, finite Step-V sums and SI endpoint integration"
  ; physicalInvolutionOwned = refl
  ; centeredParityOwned = refl
  ; contourInverseOwned = refl
  ; concretePeriodicDegreeOwned = refl
  ; siDimensionBridgeOwned = refl
  ; factorialCoefficientLeafStillOpen = refl
  ; physicalP06LeafStillOpen = refl
  ; physicalP10StillOpen = refl
  ; physicalP33StillOpen = refl
  ; terminalSubmissionStillOpen = refl
  }
