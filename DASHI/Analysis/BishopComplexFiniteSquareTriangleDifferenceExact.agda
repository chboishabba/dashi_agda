module DASHI.Analysis.BishopComplexFiniteSquareTriangleDifferenceExact where

------------------------------------------------------------------------
-- FINITE BISHOP COMPLEX SQUARE = CAUCHY TRIANGLE + UPPER WING.
--
-- The "upper wing" is NOT a new postulated summation or a generic
-- error parameter. It is exactly the square-minus-triangle residual
-- on the original Bishop complex carrier. The companion theorem
-- identifies each of its four underlying REAL coordinates with the
-- repository's already-constructed signedWingRow FINITE series,
-- whose row index i picks j in [N-i,N).
--
-- Thus this is an actual finite reindexing/splitting certificate,
-- not an infinite Cauchy product or a modulus of convergence.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexFiniteRectangleProductExact as RectangleC
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as RectangleR
import DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact as Wing
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as RowGeometry

cauchyTrianglePartial :
  (Nat → Complex.BishopComplex) →
  (Nat → Complex.BishopComplex) →
  Nat → Complex.BishopComplex
cauchyTrianglePartial left right count =
  let
    a = Complex.realTerms left
    b = Complex.imagTerms left
    c = Complex.realTerms right
    d = Complex.imagTerms right
  in
  Complex.complex
    (BishopReal._-_
      (Row.trianglePartial a c count)
      (Row.trianglePartial b d count))
    (BishopReal._+_
      (Row.trianglePartial a d count)
      (Row.trianglePartial b c count))

upperWingResidual :
  (Nat → Complex.BishopComplex) →
  (Nat → Complex.BishopComplex) →
  Nat → Complex.BishopComplex
upperWingResidual left right count =
  Algebra._-C_
    (RectangleC.rectangleComplex left right count count)
    (cauchyTrianglePartial left right count)

bishopComplexSquareCauchyWingIdentity :
  (left right : Nat → Complex.BishopComplex) →
  ∀ count →
  Complex._≈C_
    (RectangleC.rectangleComplex left right count count)
    (Algebra._+C_
      (cauchyTrianglePartial left right count)
      (upperWingResidual left right count))
bishopComplexSquareCauchyWingIdentity left right count =
  let
    r = RectangleC.rectangleComplex left right count count
    t = cauchyTrianglePartial left right count
    open BishopP.ℝ-Solver
  in
  (solve 2
    (λ a b → a ⊜ b ⊕ (a ⊖ b))
    BishopP.≃-refl
    (Complex.re r) (Complex.re t))
  ,
  (solve 2
    (λ a b → a ⊜ b ⊕ (a ⊖ b))
    BishopP.≃-refl
    (Complex.im r) (Complex.im t))

realSignedWing :
  (Nat → BishopReal.ℝ) →
  (Nat → BishopReal.ℝ) →
  Nat → BishopReal.ℝ
realSignedWing a c count =
  BishopSequence.SeriesOf (Wing.signedWingRow a c count) count

realSignedWingIsRectangleMinusTriangle :
  (a c : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._-_
      (RectangleR.rectangleSum
        a c count count)
      (Row.trianglePartial a c count))
    (realSignedWing a c count)
realSignedWingIsRectangleMinusTriangle a c count =
  BishopP.≃-trans
    (BishopP.+-cong
      (RowGeometry.rectangleSumIsNativeRows a c count count)
      (BishopP.-‿cong
        (BishopP.≃-trans
          (Row.triangleIsMertensRow a c count)
          (BishopP.≃-symm
            (RowGeometry.allRowsIsMertensRow a c count)))))
    (Wing.signedWingIsRowSeries a c count)

upperWingAsExplicitRows :
  (left right : Nat → Complex.BishopComplex) →
  ∀ count →
  Complex._≈C_
    (upperWingResidual left right count)
    (Complex.complex
      (BishopReal._-_
        (realSignedWing
          (Complex.realTerms left) (Complex.realTerms right) count)
        (realSignedWing
          (Complex.imagTerms left) (Complex.imagTerms right) count))
      (BishopReal._+_
        (realSignedWing
          (Complex.realTerms left) (Complex.imagTerms right) count)
        (realSignedWing
          (Complex.imagTerms left) (Complex.realTerms right) count)))
upperWingAsExplicitRows left right count =
  let
    a = Complex.realTerms left
    b = Complex.imagTerms left
    c = Complex.realTerms right
    d = Complex.imagTerms right
    ac = realSignedWingIsRectangleMinusTriangle a c count
    bd = realSignedWingIsRectangleMinusTriangle b d count
    ad = realSignedWingIsRectangleMinusTriangle a d count
    bc = realSignedWingIsRectangleMinusTriangle b c count
    rac = RectangleR.rectangleSum a c count count
    rbd = RectangleR.rectangleSum b d count count
    rad = RectangleR.rectangleSum a d count count
    rbc = RectangleR.rectangleSum b c count count
    tac = Row.trianglePartial a c count
    tbd = Row.trianglePartial b d count
    tad = Row.trianglePartial a d count
    tbc = Row.trianglePartial b c count

    realReassociate :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._-_ rac rbd)
          (BishopReal._-_ tac tbd))
        (BishopReal._-_
          (BishopReal._-_ rac tac)
          (BishopReal._-_ rbd tbd))
    realReassociate =
      let open BishopP.ℝ-Solver in
      solve 4
        (λ ac₁ bd₁ ac₂ bd₂ →
          (ac₁ ⊖ bd₁) ⊖ (ac₂ ⊖ bd₂)
          ⊜ (ac₁ ⊖ ac₂) ⊖ (bd₁ ⊖ bd₂))
        BishopP.≃-refl rac rbd tac tbd

    imaginaryReassociate :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._+_ rad rbc)
          (BishopReal._+_ tad tbc))
        (BishopReal._+_
          (BishopReal._-_ rad tad)
          (BishopReal._-_ rbc tbc))
    imaginaryReassociate =
      let open BishopP.ℝ-Solver in
      solve 4
        (λ ad₁ bc₁ ad₂ bc₂ →
          (ad₁ ⊕ bc₁) ⊖ (ad₂ ⊕ bc₂)
          ⊜ (ad₁ ⊖ ad₂) ⊕ (bc₁ ⊖ bc₂))
        BishopP.≃-refl rad rbc tad tbc
  in
  (BishopP.≃-trans
    realReassociate
    (BishopP.+-cong ac (BishopP.-‿cong bd)))
  ,
  (BishopP.≃-trans
    imaginaryReassociate
    (BishopP.+-cong ad bc))


------------------------------------------------------------------------
-- FOUR-SOURCE COMPONENTWISE FINITE ABSOLUTE WING DOMINATION.
--
-- The real real/both-imaginary residuals subtract, and the
-- mixed residuals add. The existing Bishop real finite Cauchy
-- wing inequality supplies the bounds for each pairing.
------------------------------------------------------------------------

positiveTriangleTail :
  (Nat → BishopReal.ℝ) →
  (Nat → BishopReal.ℝ) →
  Nat → BishopReal.ℝ
positiveTriangleTail a b count =
  BishopReal._-_
    (Row.trianglePartial (Wing.absoluteTerms a) (Wing.absoluteTerms b)
      (count + count))
    (Row.trianglePartial (Wing.absoluteTerms a) (Wing.absoluteTerms b)
      count)

originalBishopComplexWingRealAbsoluteBound :
  (left right : Nat → Complex.BishopComplex) →
  ∀ count →
  BishopReal._≤_
    (BishopReal.∣ Complex.re (upperWingResidual left right count) ∣)
    (BishopReal._+_
      (positiveTriangleTail
        (Complex.realTerms left) (Complex.realTerms right) count)
      (positiveTriangleTail
        (Complex.imagTerms left) (Complex.imagTerms right) count))
originalBishopComplexWingRealAbsoluteBound left right count =
  let
    a = Complex.realTerms left
    b = Complex.imagTerms left
    c = Complex.realTerms right
    d = Complex.imagTerms right
    rac = RectangleR.rectangleSum a c count count
    rbd = RectangleR.rectangleSum b d count count
    tac = Row.trianglePartial a c count
    tbd = Row.trianglePartial b d count
    realReassociate :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._-_ rac rbd)
          (BishopReal._-_ tac tbd))
        (BishopReal._-_
          (BishopReal._-_ rac tac)
          (BishopReal._-_ rbd tbd))
    realReassociate =
      let open BishopP.ℝ-Solver in
      solve 4
        (λ ac₁ bd₁ ac₂ bd₂ →
          (ac₁ ⊖ bd₁) ⊖ (ac₂ ⊖ bd₂)
          ⊜ (ac₁ ⊖ ac₂) ⊖ (bd₁ ⊖ bd₂))
        BishopP.≃-refl rac rbd tac tbd
  in
  BishopP.≤-respˡ-≃
    (BishopP.∣-∣-cong realReassociate)
    (BishopP.≤-trans
      (BishopP.≤-respʳ-≃
        (BishopP.+-cong
          BishopP.≃-refl
          BishopP.∣-x∣≃∣x∣)
        (BishopP.∣x+y∣≤∣x∣+∣y∣
          (BishopReal._-_ rac tac)
          (BishopReal.-_ (BishopReal._-_ rbd tbd))))
      (BishopP.+-mono-≤
        (Wing.finiteCauchyWingAbsoluteBound a c count)
        (Wing.finiteCauchyWingAbsoluteBound b d count)))

originalBishopComplexWingImagAbsoluteBound :
  (left right : Nat → Complex.BishopComplex) →
  ∀ count →
  BishopReal._≤_
    (BishopReal.∣ Complex.im (upperWingResidual left right count) ∣)
    (BishopReal._+_
      (positiveTriangleTail
        (Complex.realTerms left) (Complex.imagTerms right) count)
      (positiveTriangleTail
        (Complex.imagTerms left) (Complex.realTerms right) count))
originalBishopComplexWingImagAbsoluteBound left right count =
  let
    a = Complex.realTerms left
    b = Complex.imagTerms left
    c = Complex.realTerms right
    d = Complex.imagTerms right
    rad = RectangleR.rectangleSum a d count count
    rbc = RectangleR.rectangleSum b c count count
    tad = Row.trianglePartial a d count
    tbc = Row.trianglePartial b c count
    imaginaryReassociate :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._+_ rad rbc)
          (BishopReal._+_ tad tbc))
        (BishopReal._+_
          (BishopReal._-_ rad tad)
          (BishopReal._-_ rbc tbc))
    imaginaryReassociate =
      let open BishopP.ℝ-Solver in
      solve 4
        (λ ad₁ bc₁ ad₂ bc₂ →
          (ad₁ ⊕ bc₁) ⊖ (ad₂ ⊕ bc₂)
          ⊜ (ad₁ ⊖ ad₂) ⊕ (bc₁ ⊖ bc₂))
        BishopP.≃-refl rad rbc tad tbc
  in
  BishopP.≤-respˡ-≃
    (BishopP.∣-∣-cong imaginaryReassociate)
    (BishopP.≤-trans
      (BishopP.∣x+y∣≤∣x∣+∣y∣
        (BishopReal._-_ rad tad)
        (BishopReal._-_ rbc tbc))
      (BishopP.+-mono-≤
        (Wing.finiteCauchyWingAbsoluteBound a d count)
        (Wing.finiteCauchyWingAbsoluteBound b c count)))
