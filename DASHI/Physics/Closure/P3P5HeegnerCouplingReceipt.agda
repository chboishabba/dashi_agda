module DASHI.Physics.Closure.P3P5HeegnerCouplingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; -[1+_])
open import Data.List.Base using (List; _∷_; [])
open import Data.Empty using (⊥)

open import MonsterOntos using (SSP; p3; p5)

------------------------------------------------------------------------
-- p3-p5 Heegner coupling receipt.
--
-- This receipt corrects the p5 CM lane assignment used by the diagnostic
-- p3/p5 side route.  The p5 lane is the Heegner discriminant -7 lane with
-- j=-3375, conductor 7, modular curve X0(7), volume 8*pi/3, and units +/-1.
-- It is diagnostic only: no physical strange-mass, Cabibbo, CKM, or Yukawa
-- promotion is introduced here.

jMinus3375 : ℤ
jMinus3375 =
  -[1+ 3374 ]

discriminantMinus7 : ℤ
discriminantMinus7 =
  -[1+ 6 ]

data P3P5HeegnerCouplingStatus : Set where
  diagnosticPendingPhysicalPromotion :
    P3P5HeegnerCouplingStatus

data P3P5HeegnerCouplingBlocker : Set where
  missingPhysicalYukawaPromotion :
    P3P5HeegnerCouplingBlocker

  missingP3P5DHRIntertwiner :
    P3P5HeegnerCouplingBlocker

  missingPhysicalCKMDiagonalisation :
    P3P5HeegnerCouplingBlocker

canonicalP3P5HeegnerCouplingBlockers :
  List P3P5HeegnerCouplingBlocker
canonicalP3P5HeegnerCouplingBlockers =
  missingPhysicalYukawaPromotion
  ∷ missingP3P5DHRIntertwiner
  ∷ missingPhysicalCKMDiagonalisation
  ∷ []

p5HeegnerModuliLabel : String
p5HeegnerModuliLabel =
  "p5-lane CM moduli surface is X0(7) with j=-3375"

p5HeegnerVolumeLabel : String
p5HeegnerVolumeLabel =
  "vol(X0(7))=(pi/3)*8=8*pi/3"

p5HeegnerUnitsLabel : String
p5HeegnerUnitsLabel =
  "Heegner unit group units +/-1"

p3P5DiagnosticCouplingLabel : String
p3P5DiagnosticCouplingLabel =
  "p3-p5 Heegner coupling is recorded as diagnostic/pending physical promotion"

data P3P5PhysicalPromotion : Set where

p3P5PhysicalPromotionIsFalse :
  P3P5PhysicalPromotion →
  ⊥
p3P5PhysicalPromotionIsFalse ()

record P3P5HeegnerCouplingReceipt : Setω where
  field
    status :
      P3P5HeegnerCouplingStatus

    p3Lane :
      SSP

    p3LaneIsP3 :
      p3Lane ≡ p3

    p5Lane :
      SSP

    p5LaneIsP5 :
      p5Lane ≡ p5

    p5JInvariant :
      ℤ

    p5JInvariantIsMinus3375 :
      p5JInvariant ≡ jMinus3375

    p5Discriminant :
      ℤ

    p5DiscriminantIsMinus7 :
      p5Discriminant ≡ discriminantMinus7

    p5Conductor :
      Nat

    p5ConductorIsSeven :
      p5Conductor ≡ 7

    p5ModularCurve :
      String

    p5ModularCurveIsX07 :
      p5ModularCurve ≡ "X0(7)"

    p5ModuliStatement :
      String

    p5ModuliStatementIsCanonical :
      p5ModuliStatement ≡ p5HeegnerModuliLabel

    p5VolumeNumerator :
      Nat

    p5VolumeNumeratorIsEight :
      p5VolumeNumerator ≡ 8

    p5VolumeDenominator :
      Nat

    p5VolumeDenominatorIsThree :
      p5VolumeDenominator ≡ 3

    p5VolumeSymbol :
      String

    p5VolumeSymbolIsPi :
      p5VolumeSymbol ≡ "pi"

    p5VolumeStatement :
      String

    p5VolumeStatementIsCanonical :
      p5VolumeStatement ≡ p5HeegnerVolumeLabel

    p5UnitsStatement :
      String

    p5UnitsStatementIsCanonical :
      p5UnitsStatement ≡ p5HeegnerUnitsLabel

    p3P5DiagnosticCouplingRecorded :
      Bool

    p3P5DiagnosticCouplingRecordedIsTrue :
      p3P5DiagnosticCouplingRecorded ≡ true

    p3P5DiagnosticCouplingStatement :
      String

    p3P5DiagnosticCouplingStatementIsCanonical :
      p3P5DiagnosticCouplingStatement ≡ p3P5DiagnosticCouplingLabel

    physicalPromotionConstructed :
      Bool

    physicalPromotionConstructedIsFalse :
      physicalPromotionConstructed ≡ false

    blockers :
      List P3P5HeegnerCouplingBlocker

    blockersAreCanonical :
      blockers ≡ canonicalP3P5HeegnerCouplingBlockers

    receiptBoundary :
      List String

open P3P5HeegnerCouplingReceipt public

canonicalP3P5HeegnerCouplingReceipt :
  P3P5HeegnerCouplingReceipt
canonicalP3P5HeegnerCouplingReceipt =
  record
    { status =
        diagnosticPendingPhysicalPromotion
    ; p3Lane =
        p3
    ; p3LaneIsP3 =
        refl
    ; p5Lane =
        p5
    ; p5LaneIsP5 =
        refl
    ; p5JInvariant =
        jMinus3375
    ; p5JInvariantIsMinus3375 =
        refl
    ; p5Discriminant =
        discriminantMinus7
    ; p5DiscriminantIsMinus7 =
        refl
    ; p5Conductor =
        7
    ; p5ConductorIsSeven =
        refl
    ; p5ModularCurve =
        "X0(7)"
    ; p5ModularCurveIsX07 =
        refl
    ; p5ModuliStatement =
        p5HeegnerModuliLabel
    ; p5ModuliStatementIsCanonical =
        refl
    ; p5VolumeNumerator =
        8
    ; p5VolumeNumeratorIsEight =
        refl
    ; p5VolumeDenominator =
        3
    ; p5VolumeDenominatorIsThree =
        refl
    ; p5VolumeSymbol =
        "pi"
    ; p5VolumeSymbolIsPi =
        refl
    ; p5VolumeStatement =
        p5HeegnerVolumeLabel
    ; p5VolumeStatementIsCanonical =
        refl
    ; p5UnitsStatement =
        p5HeegnerUnitsLabel
    ; p5UnitsStatementIsCanonical =
        refl
    ; p3P5DiagnosticCouplingRecorded =
        true
    ; p3P5DiagnosticCouplingRecordedIsTrue =
        refl
    ; p3P5DiagnosticCouplingStatement =
        p3P5DiagnosticCouplingLabel
    ; p3P5DiagnosticCouplingStatementIsCanonical =
        refl
    ; physicalPromotionConstructed =
        false
    ; physicalPromotionConstructedIsFalse =
        refl
    ; blockers =
        canonicalP3P5HeegnerCouplingBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "p5 lane is recorded at j=-3375 with discriminant -7 and conductor 7"
        ∷ "p5 lane uses X0(7), vol=8*pi/3, and units +/-1"
        ∷ "This corrects the p5 lane away from the old zero-invariant assignment"
        ∷ "The p3-p5 coupling is diagnostic/pending physical promotion only"
        ∷ "No physical Yukawa, strange-mass, Cabibbo, CKM, or PDG promotion is constructed"
        ∷ []
    }

p3P5ReceiptRecordsP5JMinus3375 :
  p5JInvariant canonicalP3P5HeegnerCouplingReceipt
  ≡
  jMinus3375
p3P5ReceiptRecordsP5JMinus3375 =
  refl

p3P5ReceiptRecordsP5DiscriminantMinus7 :
  p5Discriminant canonicalP3P5HeegnerCouplingReceipt
  ≡
  discriminantMinus7
p3P5ReceiptRecordsP5DiscriminantMinus7 =
  refl

p3P5ReceiptRecordsX07Volume :
  p5VolumeStatement canonicalP3P5HeegnerCouplingReceipt
  ≡
  p5HeegnerVolumeLabel
p3P5ReceiptRecordsX07Volume =
  refl

p3P5ReceiptDoesNotPromotePhysicalCoupling :
  physicalPromotionConstructed canonicalP3P5HeegnerCouplingReceipt
  ≡
  false
p3P5ReceiptDoesNotPromotePhysicalCoupling =
  refl

p3P5NoPhysicalPromotion :
  P3P5PhysicalPromotion →
  ⊥
p3P5NoPhysicalPromotion =
  p3P5PhysicalPromotionIsFalse
