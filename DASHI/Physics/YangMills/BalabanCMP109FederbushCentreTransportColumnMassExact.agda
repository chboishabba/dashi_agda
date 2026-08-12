module DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportColumnMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Project the physical two-background quaternion estimate for the Federbush
-- centre transport onto the literal three-coordinate matrix norm used by the
-- reopening argument.
--
-- Assume the two relative-product input pairs obey the square-root-free chart
-- metric
--
--   N(U-U') + N(V-V') <= delta^2.
--
-- The physical theorem gives, on every unit Lie basis vector e_j,
--
--   N((T-T') e_j) <= 8 delta^2.
--
-- Each individual matrix entry therefore has square <= 8 delta^2 <=
-- (3 delta)^2, so its absolute value is <= 3 delta.  There are exactly three
-- Lie rows, hence every absolute column mass satisfies
--
--   col(T-T') <= 9 delta.
--
-- The deliberately coarse constant 9 is more than sufficient for the local
-- tangent modulus; it is not part of the fixed-radius Newton smallness budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; _/_; ∣_∣; NonNegative; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Four
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportPhysicalExact as Transport
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportMatrixExact as Matrix

three nine : ℚ
three = + 3 / 1
nine = + 9 / 1

imaginaryCoordinateSquareBelowNorm : ∀ coordinate value →
  Matrix.imaginaryCoordinate coordinate value
    * Matrix.imaginaryCoordinate coordinate value
  ≤ Norm.normSq value
imaginaryCoordinateSquareBelowNorm Physical.coordinateX (Q.quat q0 q1 q2 q3) =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ q0 q1 q2 q3)
      (FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.squareNonnegative q0)
          (FiniteL2.squareNonnegative q2))
        (FiniteL2.squareNonnegative q3)))
imaginaryCoordinateSquareBelowNorm Physical.coordinateY (Q.quat q0 q1 q2 q3) =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ q0 q1 q2 q3)
      (FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.squareNonnegative q0)
          (FiniteL2.squareNonnegative q1))
        (FiniteL2.squareNonnegative q3)))
imaginaryCoordinateSquareBelowNorm Physical.coordinateZ (Q.quat q0 q1 q2 q3) =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ q0 q1 q2 q3)
      (FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.squareNonnegative q0)
          (FiniteL2.squareNonnegative q1))
        (FiniteL2.squareNonnegative q2)))

squareBoundImpliesAbsoluteBound : ∀ value bound →
  0ℚ < bound →
  value * value ≤ bound * bound →
  ∣ value ∣ ≤ bound
squareBoundImpliesAbsoluteBound value bound boundPositive squareBound
  with ℚP.≤-total ∣ value ∣ bound
... | inj₁ alreadyBelow = alreadyBelow
... | inj₂ boundBelowMagnitude =
  let
    boundNonnegative : 0ℚ ≤ bound
    boundNonnegative = ℚP.<⇒≤ boundPositive

    instance
      boundNN : NonNegative bound
      boundNN = ℚ.nonNegative boundNonnegative

    absoluteSquareBound :
      ∣ value ∣ * ∣ value ∣ ≤ bound * bound
    absoluteSquareBound =
      subst
        (λ lower → lower ≤ bound * bound)
        (sym (Schur.absoluteSquareExact value))
        squareBound

    lowerProduct : bound * bound ≤ bound * ∣ value ∣
    lowerProduct = ℚP.*-monoˡ-≤-nonNeg bound boundBelowMagnitude

    absoluteSquareBelowMixed :
      ∣ value ∣ * ∣ value ∣ ≤ ∣ value ∣ * bound
    absoluteSquareBelowMixed =
      subst
        (λ upper → ∣ value ∣ * ∣ value ∣ ≤ upper)
        (ℚP.*-comm bound ∣ value ∣)
        (ℚP.≤-trans absoluteSquareBound lowerProduct)

    absolutePositive : 0ℚ < ∣ value ∣
    absolutePositive = ℚP.<-≤-trans boundPositive boundBelowMagnitude

    instance
      absolutePositiveInstance : Positive ∣ value ∣
      absolutePositiveInstance = ℚ.positive absolutePositive
  in
  ℚP.*-cancelˡ-≤-pos ∣ value ∣ absoluteSquareBelowMixed

record CentreTransportChartPair
    (u v u' v' : Q.RationalQuaternion) (delta : ℚ) : Set where
  field
    deltaPositive : 0ℚ < delta
    uUnit : Norm.normSq u ≡ + 1 / 1
    vUnit : Norm.normSq v ≡ + 1 / 1
    u'Unit : Norm.normSq u' ≡ + 1 / 1
    v'Unit : Norm.normSq v' ≡ + 1 / 1
    pairDifferenceSquare :
      Norm.normSq (Four._-q_ u u')
        + Norm.normSq (Four._-q_ v v')
      ≤ delta * delta

open CentreTransportChartPair public

basisQuaternionNormSqOne : ∀ column →
  Norm.normSq (Matrix.basisQuaternion column) ≡ + 1 / 1
basisQuaternionNormSqOne Physical.coordinateX = refl
basisQuaternionNormSqOne Physical.coordinateY = refl
basisQuaternionNormSqOne Physical.coordinateZ = refl

transportBasisDifferenceNormSq :
  ∀ u v u' v' delta →
  CentreTransportChartPair u v u' v' delta →
  ∀ column →
  Norm.normSq
    (Four._-q_
      (Transport.centreTransportAction u v (Matrix.basisQuaternion column))
      (Transport.centreTransportAction u' v' (Matrix.basisQuaternion column)))
  ≤ (+ 8 / 1) * (delta * delta)
transportBasisDifferenceNormSq u v u' v' delta chart column =
  let
    raw = Transport.centreTransportDifferenceNormSqBound
      u v u' v' (Matrix.basisQuaternion column)
      (uUnit chart) (vUnit chart) (u'Unit chart) (v'Unit chart)
    pairBound = pairDifferenceSquare chart
    scaled = Norm.scaleNonnegative (+ 8 / 1)
      (ℚP.nonNegative⁻¹ (+ 8 / 1)) pairBound
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        (+ 8 / 1)
          * (Norm.normSq (Four._-q_ u u')
            + Norm.normSq (Four._-q_ v v'))
          * Norm.normSq (Matrix.basisQuaternion column)
        ≤ upper)
      (ℚRing.solve-∀ delta)
      (subst
        (λ left →
          (+ 8 / 1)
            * (Norm.normSq (Four._-q_ u u')
              + Norm.normSq (Four._-q_ v v'))
            * left
          ≤ (+ 8 / 1) * (delta * delta))
        (basisQuaternionNormSqOne column)
        (subst
          (λ lower → lower ≤ (+ 8 / 1) * (delta * delta))
          (ℚRing.solve-∀
            (Norm.normSq (Four._-q_ u u'))
            (Norm.normSq (Four._-q_ v v')))
          scaled)))

eightBelowNine : (+ 8 / 1 : ℚ) ≤ + 9 / 1
eightBelowNine =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve [])
      (ℚP.nonNegative⁻¹ (+ 1 / 1)))

transportMatrixEntryAbsoluteBound :
  ∀ u v u' v' delta →
  CentreTransportChartPair u v u' v' delta →
  ∀ row column →
  ∣ Variation.matrixDifference
      (Matrix.centreTransportMatrix u v)
      (Matrix.centreTransportMatrix u' v') row column ∣
  ≤ three * delta
transportMatrixEntryAbsoluteBound u v u' v' delta chart row column =
  let
    qDifference = Four._-q_
      (Transport.centreTransportAction u v (Matrix.basisQuaternion column))
      (Transport.centreTransportAction u' v' (Matrix.basisQuaternion column))
    entry = Variation.matrixDifference
      (Matrix.centreTransportMatrix u v)
      (Matrix.centreTransportMatrix u' v') row column

    entryExact : entry ≡ Matrix.imaginaryCoordinate row qDifference
    entryExact = Matrix.centreTransportMatrixDifferenceEntryExact
      u v u' v' row column

    coordinateSquare :
      Matrix.imaginaryCoordinate row qDifference
        * Matrix.imaginaryCoordinate row qDifference
      ≤ (+ 8 / 1) * (delta * delta)
    coordinateSquare = ℚP.≤-trans
      (imaginaryCoordinateSquareBelowNorm row qDifference)
      (transportBasisDifferenceNormSq u v u' v' delta chart column)

    scaledEightNine :
      (delta * delta) * (+ 8 / 1)
      ≤ (delta * delta) * (+ 9 / 1)
    scaledEightNine = Norm.scaleNonnegative (delta * delta)
      (FiniteL2.squareNonnegative delta) eightBelowNine

    eightDeltaBelowNineDelta :
      (+ 8 / 1) * (delta * delta)
      ≤ (+ 9 / 1) * (delta * delta)
    eightDeltaBelowNineDelta =
      subst
        (λ lower → lower ≤ (+ 9 / 1) * (delta * delta))
        (ℚP.*-comm (delta * delta) (+ 8 / 1))
        (subst
          (λ upper → (delta * delta) * (+ 8 / 1) ≤ upper)
          (ℚP.*-comm (delta * delta) (+ 9 / 1))
          scaledEightNine)

    belowNine :
      Matrix.imaginaryCoordinate row qDifference
        * Matrix.imaginaryCoordinate row qDifference
      ≤ (three * delta) * (three * delta)
    belowNine = ℚP.≤-trans coordinateSquare
      (subst
        (λ upper → (+ 8 / 1) * (delta * delta) ≤ upper)
        (ℚRing.solve-∀ delta)
        eightDeltaBelowNineDelta)

    instance
      deltaPositiveInstance : Positive delta
      deltaPositiveInstance = ℚ.positive (deltaPositive chart)

      threeDeltaPositiveInstance : Positive (three * delta)
      threeDeltaPositiveInstance = ℚP.pos*pos⇒pos three delta

    threeDeltaPositive : 0ℚ < three * delta
    threeDeltaPositive = ℚP.positive⁻¹ (three * delta)
  in
  subst
    (λ selected → ∣ selected ∣ ≤ three * delta)
    (sym entryExact)
    (squareBoundImpliesAbsoluteBound
      (Matrix.imaginaryCoordinate row qDifference)
      (three * delta) threeDeltaPositive belowNine)

transportMatrixColumnMassBound :
  ∀ u v u' v' delta →
  CentreTransportChartPair u v u' v' delta →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (Matrix.centreTransportMatrix u v)
      (Matrix.centreTransportMatrix u' v')) column
  ≤ nine * delta
transportMatrixColumnMassBound u v u' v' delta chart column =
  let
    ex = transportMatrixEntryAbsoluteBound u v u' v' delta chart
      Physical.coordinateX column
    ey = transportMatrixEntryAbsoluteBound u v u' v' delta chart
      Physical.coordinateY column
    ez = transportMatrixEntryAbsoluteBound u v u' v' delta chart
      Physical.coordinateZ column
  in
  subst
    (λ upper →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference
          (Matrix.centreTransportMatrix u v)
          (Matrix.centreTransportMatrix u' v')) column
      ≤ upper)
    (ℚRing.solve-∀ delta)
    (ℚP.+-mono-≤ ex (ℚP.+-mono-≤ ey ez))

cmp109FederbushCentreTransportEntryModulusLevel : ProofLevel
cmp109FederbushCentreTransportEntryModulusLevel = machineChecked

cmp109FederbushCentreTransportColumnMassModulusLevel : ProofLevel
cmp109FederbushCentreTransportColumnMassModulusLevel = machineChecked
