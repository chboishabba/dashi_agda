module DASHI.Physics.Closure.NSWholeSpaceBishopComplex3CauchyPSDExact where

------------------------------------------------------------------------
-- A / FINITE BISHOP C^3 CAUCHY-RESOLVENT PSD
--
-- Lift NSWholeSpaceBishopFiniteCauchyPSDExact coordinatewise to the literal
-- BishopComplex3 carrier used by the whole-space Fourier realization.
--
-- The real Hermitian pairing is exactly the sum of six real-coordinate
-- products.  Therefore the finite Cauchy-resolvent Hermitian quadratic form is
-- the sum of six scalar Cauchy quadratic forms, each already nonnegative.
--
-- No norm majorisation, absolute value, Laplace transform, spectral theorem,
-- improper integral, or continuum limit is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanRawGramOutputQuadraticExact as Gram
import DASHI.Physics.Closure.NSWholeSpaceBishopFiniteCauchyPSDExact as Scalar

record PositiveRateComplex3Cell : Set where
  constructor positive-rate-complex3-cell
  field
    rate : BishopReal.ℝ
    value : Physical.BishopComplex3
    ratePositive : BishopReal._<_ BishopReal.0ℝ rate

open PositiveRateComplex3Cell public

xReal xImag yReal yImag zReal zImag :
  Physical.BishopComplex3 → BishopReal.ℝ
xReal value = Physical.realPart (Physical.cx value)
xImag value = Physical.imaginaryPart (Physical.cx value)
yReal value = Physical.realPart (Physical.cy value)
yImag value = Physical.imaginaryPart (Physical.cy value)
zReal value = Physical.realPart (Physical.cz value)
zImag value = Physical.imaginaryPart (Physical.cz value)

toScalarPoint :
  (Physical.BishopComplex3 → BishopReal.ℝ) →
  PositiveRateComplex3Cell →
  Scalar.PositiveRatePoint
toScalarPoint coordinate cell =
  Scalar.positive-rate-point
    (rate cell)
    (coordinate (value cell))
    (ratePositive cell)

coordinatePoints :
  (Physical.BishopComplex3 → BishopReal.ℝ) →
  List PositiveRateComplex3Cell →
  List Scalar.PositiveRatePoint
coordinatePoints coordinate =
  map (toScalarPoint coordinate)

coordinateCauchyForm :
  (Physical.BishopComplex3 → BishopReal.ℝ) →
  List PositiveRateComplex3Cell →
  BishopReal.ℝ
coordinateCauchyForm coordinate cells =
  Scalar.storedCauchyQuadratic
    (coordinatePoints coordinate cells)

coordinateCauchyFormNonnegative :
  (coordinate : Physical.BishopComplex3 → BishopReal.ℝ) →
  (cells : List PositiveRateComplex3Cell) →
  BishopReal.NonNegative
    (coordinateCauchyForm coordinate cells)
coordinateCauchyFormNonnegative coordinate cells =
  Scalar.storedCauchyQuadraticNonnegative
    (coordinatePoints coordinate cells)

sumSix :
  BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ →
  BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ →
  BishopReal.ℝ
sumSix a b c d e f =
  BishopReal._+_ a
    (BishopReal._+_ b
      (BishopReal._+_ c
        (BishopReal._+_ d
          (BishopReal._+_ e f))))

hermitianCauchyForm :
  List PositiveRateComplex3Cell →
  BishopReal.ℝ
hermitianCauchyForm cells =
  sumSix
    (coordinateCauchyForm xReal cells)
    (coordinateCauchyForm xImag cells)
    (coordinateCauchyForm yReal cells)
    (coordinateCauchyForm yImag cells)
    (coordinateCauchyForm zReal cells)
    (coordinateCauchyForm zImag cells)

hermitianCauchyFormNonnegative :
  (cells : List PositiveRateComplex3Cell) →
  BishopReal.NonNegative (hermitianCauchyForm cells)
hermitianCauchyFormNonnegative cells =
  BishopP.nonNegx,y⇒nonNegx+y
    (coordinateCauchyFormNonnegative xReal cells)
    (BishopP.nonNegx,y⇒nonNegx+y
      (coordinateCauchyFormNonnegative xImag cells)
      (BishopP.nonNegx,y⇒nonNegx+y
        (coordinateCauchyFormNonnegative yReal cells)
        (BishopP.nonNegx,y⇒nonNegx+y
          (coordinateCauchyFormNonnegative yImag cells)
          (BishopP.nonNegx,y⇒nonNegx+y
            (coordinateCauchyFormNonnegative zReal cells)
            (coordinateCauchyFormNonnegative zImag cells)))))

------------------------------------------------------------------------
-- Atom-level same-object identification.
------------------------------------------------------------------------

cauchyEntry :
  PositiveRateComplex3Cell →
  PositiveRateComplex3Cell →
  BishopReal.ℝ
cauchyEntry left right =
  Scalar.cauchyEntry
    (toScalarPoint xReal left)
    (toScalarPoint xReal right)

coordinateAtom :
  (Physical.BishopComplex3 → BishopReal.ℝ) →
  PositiveRateComplex3Cell →
  PositiveRateComplex3Cell →
  BishopReal.ℝ
coordinateAtom coordinate left right =
  BishopReal._*_
    (cauchyEntry left right)
    (BishopReal._*_
      (coordinate (value left))
      (coordinate (value right)))

sixCoordinateAtom :
  PositiveRateComplex3Cell →
  PositiveRateComplex3Cell →
  BishopReal.ℝ
sixCoordinateAtom left right =
  sumSix
    (coordinateAtom xReal left right)
    (coordinateAtom xImag left right)
    (coordinateAtom yReal left right)
    (coordinateAtom yImag left right)
    (coordinateAtom zReal left right)
    (coordinateAtom zImag left right)

hermitianAtom :
  PositiveRateComplex3Cell →
  PositiveRateComplex3Cell →
  BishopReal.ℝ
hermitianAtom left right =
  BishopReal._*_
    (cauchyEntry left right)
    (Gram.realHermitianCross
      (value left)
      (value right))

hermitianAtomIsSixCoordinates :
  (left right : PositiveRateComplex3Cell) →
  BishopReal._≃_
    (hermitianAtom left right)
    (sixCoordinateAtom left right)
hermitianAtomIsSixCoordinates left right =
  let
    k = cauchyEntry left right
    lx = xReal (value left)
    lxi = xImag (value left)
    ly = yReal (value left)
    lyi = yImag (value left)
    lz = zReal (value left)
    lzi = zImag (value left)
    rx = xReal (value right)
    rxi = xImag (value right)
    ry = yReal (value right)
    ryi = yImag (value right)
    rz = zReal (value right)
    rzi = zImag (value right)
    open BishopP.ℝ-Solver
  in
  solve 13
    (λ k' lx' lxi' ly' lyi' lz' lzi'
       rx' rxi' ry' ryi' rz' rzi' →
      k' ⊗
        ((lx' ⊗ rx' ⊕ lxi' ⊗ rxi')
          ⊕
          ((ly' ⊗ ry' ⊕ lyi' ⊗ ryi')
            ⊕ (lz' ⊗ rz' ⊕ lzi' ⊗ rzi')))
      ⊜
      (k' ⊗ (lx' ⊗ rx'))
      ⊕
      ((k' ⊗ (lxi' ⊗ rxi'))
        ⊕
        ((k' ⊗ (ly' ⊗ ry'))
          ⊕
          ((k' ⊗ (lyi' ⊗ ryi'))
            ⊕
            ((k' ⊗ (lz' ⊗ rz'))
              ⊕ (k' ⊗ (lzi' ⊗ rzi'))))))
    BishopP.≃-refl
    k lx lxi ly lyi lz lzi rx rxi ry ryi rz rzi

finiteBishopComplex3CauchyPSDClosed : Bool
finiteBishopComplex3CauchyPSDClosed = true

atomMatchesExistingRealHermitianCross : Bool
atomMatchesExistingRealHermitianCross = true

normMajorizationUsed : Bool
normMajorizationUsed = false

absoluteValueUsed : Bool
absoluteValueUsed = false

continuumLimitTakenHere : Bool
continuumLimitTakenHere = false

clayPromotion : Bool
clayPromotion = false

finiteBishopComplex3CauchyPSDClosedIsTrue :
  finiteBishopComplex3CauchyPSDClosed ≡ true
finiteBishopComplex3CauchyPSDClosedIsTrue = refl

atomMatchesExistingRealHermitianCrossIsTrue :
  atomMatchesExistingRealHermitianCross ≡ true
atomMatchesExistingRealHermitianCrossIsTrue = refl

normMajorizationUsedIsFalse :
  normMajorizationUsed ≡ false
normMajorizationUsedIsFalse = refl

absoluteValueUsedIsFalse :
  absoluteValueUsed ≡ false
absoluteValueUsedIsFalse = refl

continuumLimitTakenHereIsFalse :
  continuumLimitTakenHere ≡ false
continuumLimitTakenHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
