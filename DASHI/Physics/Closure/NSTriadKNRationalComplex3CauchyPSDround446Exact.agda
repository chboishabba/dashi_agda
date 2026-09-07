module DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact where

------------------------------------------------------------------------
-- ROUND446 / LIFT R445 CAUCHY PSD TO THE LITERAL RATIONAL COMPLEX3 CARRIER
--
-- R179's real Hermitian pairing on rational C^3 is literally the sum of six
-- real-coordinate products.  Therefore the full Cauchy-weighted Hermitian form
-- is the sum of six scalar R445 Cauchy forms.  Positivity follows coordinate by
-- coordinate; no norm inequality, Cauchy--Schwarz, spectral theorem, square
-- root, exponential or integral is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalFiniteCauchyPSDCompilerRound445Exact as R445

F : C3.RealField _
F = Rational.rationalRealField

record PositiveRateComplex3Cell : Set where
  constructor positive-rate-complex3-cell
  field
    rate : ℚ
    value : C3.Complex3 F
    ratePositive : Positive rate

open PositiveRateComplex3Cell public

xReal xImag yReal yImag zReal zImag : C3.Complex3 F → ℚ
xReal (C3.complex3 (C3.complex xr xi) y z) = xr
xImag (C3.complex3 (C3.complex xr xi) y z) = xi
yReal (C3.complex3 x (C3.complex yr yi) z) = yr
yImag (C3.complex3 x (C3.complex yr yi) z) = yi
zReal (C3.complex3 x y (C3.complex zr zi)) = zr
zImag (C3.complex3 x y (C3.complex zr zi)) = zi

coordinatePoints :
  (C3.Complex3 F → ℚ) →
  List PositiveRateComplex3Cell →
  List R445.PositiveRatePoint
coordinatePoints coordinate [] = []
coordinatePoints coordinate (cell ∷ rest) =
  R445.positive-rate-point
    (rate cell)
    (coordinate (value cell))
    (ratePositive cell)
  ∷ coordinatePoints coordinate rest

coordinateCauchyForm :
  (C3.Complex3 F → ℚ) →
  List PositiveRateComplex3Cell → ℚ
coordinateCauchyForm coordinate cells =
  R445.storedCauchyQuadratic (coordinatePoints coordinate cells)

complex3CauchyForm : List PositiveRateComplex3Cell → ℚ
complex3CauchyForm cells =
  coordinateCauchyForm xReal cells
  + coordinateCauchyForm xImag cells
  + coordinateCauchyForm yReal cells
  + coordinateCauchyForm yImag cells
  + coordinateCauchyForm zReal cells
  + coordinateCauchyForm zImag cells

coordinateCauchyFormNonnegative :
  (coordinate : C3.Complex3 F → ℚ) →
  (cells : List PositiveRateComplex3Cell) →
  0ℚ ≤ coordinateCauchyForm coordinate cells
coordinateCauchyFormNonnegative coordinate cells =
  R445.storedCauchyQuadraticNonnegative (coordinatePoints coordinate cells)

complex3CauchyFormNonnegative :
  (cells : List PositiveRateComplex3Cell) →
  0ℚ ≤ complex3CauchyForm cells
complex3CauchyFormNonnegative cells =
  Rational.addNonnegative
    (Rational.addNonnegative
      (Rational.addNonnegative
        (Rational.addNonnegative
          (Rational.addNonnegative
            (coordinateCauchyFormNonnegative xReal cells)
            (coordinateCauchyFormNonnegative xImag cells))
          (coordinateCauchyFormNonnegative yReal cells))
        (coordinateCauchyFormNonnegative yImag cells))
      (coordinateCauchyFormNonnegative zReal cells))
    (coordinateCauchyFormNonnegative zImag cells)

round446LiteralRationalComplex3CauchyPSDClosed : Bool
round446LiteralRationalComplex3CauchyPSDClosed = true

round446UsesR179SixRealCoordinateMeaning : Bool
round446UsesR179SixRealCoordinateMeaning = true

round446NormMajorizationUsed : Bool
round446NormMajorizationUsed = false

round446ImproperIntegralUsed : Bool
round446ImproperIntegralUsed = false

round446PhysicalDoubleMixedCarrierAttached : Bool
round446PhysicalDoubleMixedCarrierAttached = false

round446PackageAClosed : Bool
round446PackageAClosed = false

round446ClayPromotion : Bool
round446ClayPromotion = false

round446NormMajorizationUsedIsFalse : round446NormMajorizationUsed ≡ false
round446NormMajorizationUsedIsFalse = refl
