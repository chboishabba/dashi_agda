module DASHI.Foundations.JacobianThreeSheetTriadicBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ)

open import Verification.JacobianCounterexampleKernel as J
  using
    ( Point3
    ; F
    ; target
    ; pZero
    ; pPositive
    ; pNegative
    ; pZeroImage
    ; pPositiveImage
    ; pNegativeImage
    ; xCoordinate
    ; zeroQ
    ; oneR
    ; minusOneR
    )

------------------------------------------------------------------------
-- The labelling follows an actual algebraic three-point fibre.  It does not
-- infer the fibre from numerology or from decimal digits.

data BalancedTrit : Set where
  negativeTrit zeroTrit positiveTrit : BalancedTrit

sheetPoint : BalancedTrit → Point3
sheetPoint negativeTrit = pNegative
sheetPoint zeroTrit = pZero
sheetPoint positiveTrit = pPositive

sheetXCoordinate : BalancedTrit → ℚ
sheetXCoordinate trit = xCoordinate (sheetPoint trit)

negativeCoordinateChecked : sheetXCoordinate negativeTrit ≡ minusOneR
negativeCoordinateChecked = refl

zeroCoordinateChecked : sheetXCoordinate zeroTrit ≡ zeroQ
zeroCoordinateChecked = refl

positiveCoordinateChecked : sheetXCoordinate positiveTrit ≡ oneR
positiveCoordinateChecked = refl

allDisplayedSheetsMapToTarget :
  (trit : BalancedTrit) →
  F (sheetPoint trit) ≡ target
allDisplayedSheetsMapToTarget negativeTrit = pNegativeImage
allDisplayedSheetsMapToTarget zeroTrit = pZeroImage
allDisplayedSheetsMapToTarget positiveTrit = pPositiveImage

record ThreeSheetTriadicReceipt : Set where
  constructor mkThreeSheetTriadicReceipt
  field
    exactThreePointFibreUsed : Bool
    negativeZeroPositiveCoordinatesChecked : Bool
    everyLabelMapsToDisplayedTarget : Bool
    genericFibreDegreeDeclaredThree : Bool
    genericFibreDegreeDeclaredThreeIsFalse :
      genericFibreDegreeDeclaredThree ≡ false
    tritLabelsUsedToProveExistence : Bool
    tritLabelsUsedToProveExistenceIsFalse :
      tritLabelsUsedToProveExistence ≡ false
    interpretation : String

threeSheetTriadicReceipt : ThreeSheetTriadicReceipt
threeSheetTriadicReceipt =
  mkThreeSheetTriadicReceipt
    true true true
    false refl
    false refl
    "the balanced labels -1, 0 and +1 are assigned after checking an exact three-point fibre; one exceptional fibre does not by itself prove the generic fibre degree"
