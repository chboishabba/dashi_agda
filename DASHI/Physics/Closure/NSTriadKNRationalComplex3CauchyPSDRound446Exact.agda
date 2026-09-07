module DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact where

------------------------------------------------------------------------
-- ROUND446 / LIFT R445 CAUCHY PSD TO THE LITERAL RATIONAL COMPLEX3 CARRIER
--
-- R179's real Hermitian pairing on rational C^3 is literally the sum of six
-- real-coordinate products.  This file proves the finite identification, not
-- merely the coordinatewise positivity:
--
--   sum_{i,j} K_ij Re<A_i,A_j>
--     = sum over the six real coordinates Q_K(coord),
--
-- where K_ij is R443's literal rational Cauchy reciprocal.  R445 pays every
-- scalar coordinate form, so the exact Hermitian form is nonnegative.
--
-- No norm inequality, Cauchy--Schwarz, square root, spectral theorem,
-- exponential, improper integral, or completeness authority is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; Positive; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNFiniteKernelRankOneQuadraticSplitRound444Exact as R444
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

sumSix : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
sumSix a b c d e f = a + b + c + d + e + f

realHermitianCrossIsSixCoordinates :
  (left right : C3.Complex3 F) →
  R179.realHermitianCross left right
  ≡ sumSix
      (xReal left * xReal right)
      (xImag left * xImag right)
      (yReal left * yReal right)
      (yImag left * yImag right)
      (zReal left * zReal right)
      (zImag left * zImag right)
realHermitianCrossIsSixCoordinates
    (C3.complex3
      (C3.complex ax ai) (C3.complex ay ayi) (C3.complex az azi))
    (C3.complex3
      (C3.complex bx bi) (C3.complex by byi) (C3.complex bz bzi)) =
  refl

cauchyKernel : PositiveRateComplex3Cell → PositiveRateComplex3Cell → ℚ
cauchyKernel left right = R443.cauchyEntry (rate left) (rate right)

toCoordinatePoint :
  (C3.Complex3 F → ℚ) →
  PositiveRateComplex3Cell →
  R445.PositiveRatePoint
toCoordinatePoint coordinate cell =
  R445.positive-rate-point
    (rate cell)
    (coordinate (value cell))
    (ratePositive cell)

coordinatePoints :
  (C3.Complex3 F → ℚ) →
  List PositiveRateComplex3Cell →
  List R445.PositiveRatePoint
coordinatePoints coordinate [] = []
coordinatePoints coordinate (cell ∷ rest) =
  toCoordinatePoint coordinate cell ∷ coordinatePoints coordinate rest

coordinateRow :
  (C3.Complex3 F → ℚ) →
  PositiveRateComplex3Cell →
  List PositiveRateComplex3Cell → ℚ
coordinateRow coordinate head [] = 0ℚ
coordinateRow coordinate head (cell ∷ rest) =
  cauchyKernel head cell
    * coordinate (value cell)
  + coordinateRow coordinate head rest

coordinateScalarForm :
  (C3.Complex3 F → ℚ) →
  List PositiveRateComplex3Cell → ℚ
coordinateScalarForm coordinate [] = 0ℚ
coordinateScalarForm coordinate (head ∷ rest) =
  cauchyKernel head head
    * coordinate (value head) * coordinate (value head)
  + (1ℚ + 1ℚ) * coordinate (value head)
      * coordinateRow coordinate head rest
  + coordinateScalarForm coordinate rest

pointRowIsCoordinateRow :
  (coordinate : C3.Complex3 F → ℚ) →
  (head : PositiveRateComplex3Cell) →
  (rest : List PositiveRateComplex3Cell) →
  R444.rowSum
    R445.cauchyKernel
    R445.storedCoefficient
    (toCoordinatePoint coordinate head)
    (coordinatePoints coordinate rest)
  ≡ coordinateRow coordinate head rest
pointRowIsCoordinateRow coordinate head [] = refl
pointRowIsCoordinateRow coordinate head (cell ∷ rest) =
  cong₂ _+_ refl (pointRowIsCoordinateRow coordinate head rest)

coordinateStoredFormIsScalarForm :
  (coordinate : C3.Complex3 F → ℚ) →
  (cells : List PositiveRateComplex3Cell) →
  R445.storedCauchyQuadratic (coordinatePoints coordinate cells)
  ≡ coordinateScalarForm coordinate cells
coordinateStoredFormIsScalarForm coordinate [] = refl
coordinateStoredFormIsScalarForm coordinate (head ∷ rest) =
  cong₂ _+_
    (cong₂ _+_
      refl
      (cong₂ _*_
        (cong₂ _*_ refl refl)
        (pointRowIsCoordinateRow coordinate head rest)))
    (coordinateStoredFormIsScalarForm coordinate rest)

coordinateScalarFormNonnegative :
  (coordinate : C3.Complex3 F → ℚ) →
  (cells : List PositiveRateComplex3Cell) →
  0ℚ ≤ coordinateScalarForm coordinate cells
coordinateScalarFormNonnegative coordinate cells =
  let
    source = R445.storedCauchyQuadraticNonnegative
      (coordinatePoints coordinate cells)
  in
  Relation.Binary.PropositionalEquality.subst
    (0ℚ ≤_)
    (coordinateStoredFormIsScalarForm coordinate cells)
    source

hermitianRow :
  PositiveRateComplex3Cell →
  List PositiveRateComplex3Cell → ℚ
hermitianRow head [] = 0ℚ
hermitianRow head (cell ∷ rest) =
  cauchyKernel head cell
    * R179.realHermitianCross (value head) (value cell)
  + hermitianRow head rest

hermitianCauchyForm : List PositiveRateComplex3Cell → ℚ
hermitianCauchyForm [] = 0ℚ
hermitianCauchyForm (head ∷ rest) =
  cauchyKernel head head
    * R179.realHermitianCross (value head) (value head)
  + (1ℚ + 1ℚ) * hermitianRow head rest
  + hermitianCauchyForm rest

hermitianRowIsSixCoordinateRows :
  (head : PositiveRateComplex3Cell) →
  (rest : List PositiveRateComplex3Cell) →
  hermitianRow head rest
  ≡ sumSix
      (xReal (value head) * coordinateRow xReal head rest)
      (xImag (value head) * coordinateRow xImag head rest)
      (yReal (value head) * coordinateRow yReal head rest)
      (yImag (value head) * coordinateRow yImag head rest)
      (zReal (value head) * coordinateRow zReal head rest)
      (zImag (value head) * coordinateRow zImag head rest)
hermitianRowIsSixCoordinateRows head [] =
  solve
    ( xReal (value head) ∷ xImag (value head)
    ∷ yReal (value head) ∷ yImag (value head)
    ∷ zReal (value head) ∷ zImag (value head) ∷ [])
hermitianRowIsSixCoordinateRows head (cell ∷ rest) =
  let
    K = cauchyKernel head cell
    cross = realHermitianCrossIsSixCoordinates (value head) (value cell)
    tail = hermitianRowIsSixCoordinateRows head rest
  in
  trans
    (cong₂ _+_ (cong₂ _*_ refl cross) tail)
    (solve
      ( K
      ∷ xReal (value head) ∷ xImag (value head)
      ∷ yReal (value head) ∷ yImag (value head)
      ∷ zReal (value head) ∷ zImag (value head)
      ∷ xReal (value cell) ∷ xImag (value cell)
      ∷ yReal (value cell) ∷ yImag (value cell)
      ∷ zReal (value cell) ∷ zImag (value cell)
      ∷ coordinateRow xReal head rest
      ∷ coordinateRow xImag head rest
      ∷ coordinateRow yReal head rest
      ∷ coordinateRow yImag head rest
      ∷ coordinateRow zReal head rest
      ∷ coordinateRow zImag head rest ∷ []))

sixCoordinateScalarForms : List PositiveRateComplex3Cell → ℚ
sixCoordinateScalarForms cells =
  sumSix
    (coordinateScalarForm xReal cells)
    (coordinateScalarForm xImag cells)
    (coordinateScalarForm yReal cells)
    (coordinateScalarForm yImag cells)
    (coordinateScalarForm zReal cells)
    (coordinateScalarForm zImag cells)

hermitianCauchyFormIsSixCoordinateForms :
  (cells : List PositiveRateComplex3Cell) →
  hermitianCauchyForm cells ≡ sixCoordinateScalarForms cells
hermitianCauchyFormIsSixCoordinateForms [] = refl
hermitianCauchyFormIsSixCoordinateForms (head ∷ rest) =
  let
    K = cauchyKernel head head
    diagonal = realHermitianCrossIsSixCoordinates (value head) (value head)
    rows = hermitianRowIsSixCoordinateRows head rest
    tail = hermitianCauchyFormIsSixCoordinateForms rest
  in
  trans
    (cong₂ _+_
      (cong₂ _+_
        (cong₂ _*_ refl diagonal)
        (cong₂ _*_ refl rows))
      tail)
    (solve
      ( K
      ∷ xReal (value head) ∷ xImag (value head)
      ∷ yReal (value head) ∷ yImag (value head)
      ∷ zReal (value head) ∷ zImag (value head)
      ∷ coordinateRow xReal head rest
      ∷ coordinateRow xImag head rest
      ∷ coordinateRow yReal head rest
      ∷ coordinateRow yImag head rest
      ∷ coordinateRow zReal head rest
      ∷ coordinateRow zImag head rest
      ∷ coordinateScalarForm xReal rest
      ∷ coordinateScalarForm xImag rest
      ∷ coordinateScalarForm yReal rest
      ∷ coordinateScalarForm yImag rest
      ∷ coordinateScalarForm zReal rest
      ∷ coordinateScalarForm zImag rest ∷ []))

sixCoordinateScalarFormsNonnegative :
  (cells : List PositiveRateComplex3Cell) →
  0ℚ ≤ sixCoordinateScalarForms cells
sixCoordinateScalarFormsNonnegative cells =
  Rational.addNonnegative
    (Rational.addNonnegative
      (Rational.addNonnegative
        (Rational.addNonnegative
          (Rational.addNonnegative
            (coordinateScalarFormNonnegative xReal cells)
            (coordinateScalarFormNonnegative xImag cells))
          (coordinateScalarFormNonnegative yReal cells))
        (coordinateScalarFormNonnegative yImag cells))
      (coordinateScalarFormNonnegative zReal cells))
    (coordinateScalarFormNonnegative zImag cells)

hermitianCauchyFormNonnegative :
  (cells : List PositiveRateComplex3Cell) →
  0ℚ ≤ hermitianCauchyForm cells
hermitianCauchyFormNonnegative cells =
  Relation.Binary.PropositionalEquality.subst
    (0ℚ ≤_)
    (sym (hermitianCauchyFormIsSixCoordinateForms cells))
    (sixCoordinateScalarFormsNonnegative cells)

round446LiteralR179HermitianCauchyPSDClosed : Bool
round446LiteralR179HermitianCauchyPSDClosed = true

round446SixCoordinateEqualityProofBearing : Bool
round446SixCoordinateEqualityProofBearing = true

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
