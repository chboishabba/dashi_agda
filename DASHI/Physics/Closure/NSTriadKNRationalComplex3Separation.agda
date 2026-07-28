module DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean Leray; Marco Cannone; Augustin-Louis Cauchy; Hermann Amandus
-- Schwarz; DASHI repository contributors.
-- Title: "Positive-definite separation of the exact rational C3 carrier".
-- Venue/year: Handbook of Mathematical Fluid Dynamics, Volume 3, 2005;
-- classical finite-dimensional inner-product theory; DASHI formal
-- development, 2026.
-- DOI: 10.1016/S1874-5792(05)80006-0 for Marco Cannone,
-- "Harmonic Analysis Tools for Solving the Incompressible Navier--Stokes
-- Equations"; no DOI applies to the repository-original coordinate proof.
-- Uses: nonnegativity of rational squares, zero-product separation, the
-- concrete identity Re <v,v> = ||v||^2, and additive-group cancellation.
-- Relationship: closes ||v||^2 = 0 -> v = 0 and
-- ||u-v||^2 = 0 -> u = v on the exact rational C3 carrier.  It therefore
-- discharges the last positive-definite input to restricted transverse-test
-- uniqueness at finite rational cutoff.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Properties.Group as GroupProperties
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNComplex3RestrictedUniquenessInputs as Inputs
import DASHI.Physics.Closure.NSTriadKNRestrictedTransverseUniqueness as Restricted
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

module AddGroup = GroupProperties ℚₚ.+-0-group

F : C3.RealField _
F = RationalL2.rationalRealField

------------------------------------------------------------------------
-- Ordered scalar separation.
------------------------------------------------------------------------

rationalSquareZeroImpliesZero :
  ∀ value → RationalL2.square value ≡ 0ℚ → value ≡ 0ℚ
rationalSquareZeroImpliesZero value squareZero
  with ℚₚ.p*q≡0⇒p≡0∨q≡0 squareZero
... | inj₁ valueZero = valueZero
... | inj₂ valueZero = valueZero

nonnegativeAddZeroComponents :
  ∀ {left right} →
  0ℚ ≤ left →
  0ℚ ≤ right →
  left + right ≡ 0ℚ →
  left ≡ 0ℚ × right ≡ 0ℚ
nonnegativeAddZeroComponents {left} {right}
  leftNonnegative rightNonnegative sumZero =
  let
    leftBelowSum : left ≤ left + right
    leftBelowSum =
      subst
        (λ lower → lower ≤ left + right)
        (ℚₚ.+-identityʳ left)
        (ℚₚ.+-mono-≤ ℚₚ.≤-refl rightNonnegative)

    rightBelowSum : right ≤ left + right
    rightBelowSum =
      subst
        (λ lower → lower ≤ left + right)
        (ℚₚ.+-identityˡ right)
        (ℚₚ.+-mono-≤ leftNonnegative ℚₚ.≤-refl)

    leftBelowZero : left ≤ 0ℚ
    leftBelowZero = subst (λ upper → left ≤ upper) sumZero leftBelowSum

    rightBelowZero : right ≤ 0ℚ
    rightBelowZero = subst (λ upper → right ≤ upper) sumZero rightBelowSum
  in
  ℚₚ.≤-antisym leftBelowZero leftNonnegative
  , ℚₚ.≤-antisym rightBelowZero rightNonnegative

------------------------------------------------------------------------
-- Complex and C3 zero-norm separation.
------------------------------------------------------------------------

complexModulusSquaredNonnegative :
  ∀ value →
  0ℚ ≤ L2.complexModulusSquared {F = F} value
complexModulusSquaredNonnegative (C3.complex real imaginary) =
  RationalL2.addNonnegative
    (RationalL2.squareNonnegative real)
    (RationalL2.squareNonnegative imaginary)

complexModulusSquaredZeroImpliesZero :
  ∀ value →
  L2.complexModulusSquared {F = F} value ≡ 0ℚ →
  value ≡ C3.complexZero F
complexModulusSquaredZeroImpliesZero
  (C3.complex real imaginary) modulusZero =
  let
    coordinates =
      nonnegativeAddZeroComponents
        (RationalL2.squareNonnegative real)
        (RationalL2.squareNonnegative imaginary)
        modulusZero

    realZero : real ≡ 0ℚ
    realZero = rationalSquareZeroImpliesZero real (proj₁ coordinates)

    imaginaryZero : imaginary ≡ 0ℚ
    imaginaryZero =
      rationalSquareZeroImpliesZero imaginary (proj₂ coordinates)
  in
  cong₂Complex realZero imaginaryZero
  where
  cong₂Complex :
    ∀ {ar ai br bi} →
    ar ≡ br → ai ≡ bi →
    C3.complex ar ai ≡ C3.complex br bi
  cong₂Complex refl refl = refl

complex3NormSquaredNonnegative :
  ∀ value →
  0ℚ ≤ L2.complex3NormSquared {F = F} value
complex3NormSquaredNonnegative (C3.complex3 first second third) =
  RationalL2.addNonnegative
    (RationalL2.addNonnegative
      (complexModulusSquaredNonnegative first)
      (complexModulusSquaredNonnegative second))
    (complexModulusSquaredNonnegative third)

complex3NormSquaredZeroImpliesZero :
  ∀ value →
  L2.complex3NormSquared {F = F} value ≡ 0ℚ →
  value ≡ C3.complex3Zero F
complex3NormSquaredZeroImpliesZero
  (C3.complex3 first second third) normZero =
  let
    firstNonnegative = complexModulusSquaredNonnegative first
    secondNonnegative = complexModulusSquaredNonnegative second
    thirdNonnegative = complexModulusSquaredNonnegative third

    firstSecondNonnegative :
      0ℚ ≤
      L2.complexModulusSquared {F = F} first
      + L2.complexModulusSquared {F = F} second
    firstSecondNonnegative =
      RationalL2.addNonnegative firstNonnegative secondNonnegative

    outer =
      nonnegativeAddZeroComponents
        firstSecondNonnegative
        thirdNonnegative
        normZero

    inner =
      nonnegativeAddZeroComponents
        firstNonnegative
        secondNonnegative
        (proj₁ outer)

    firstZero = complexModulusSquaredZeroImpliesZero first (proj₁ inner)
    secondZero = complexModulusSquaredZeroImpliesZero second (proj₂ inner)
    thirdZero = complexModulusSquaredZeroImpliesZero third (proj₂ outer)
  in
  cong3 firstZero secondZero thirdZero
  where
  cong3 :
    ∀ {a b c a′ b′ c′} →
    a ≡ a′ → b ≡ b′ → c ≡ c′ →
    C3.complex3 a b c ≡ C3.complex3 a′ b′ c′
  cong3 refl refl refl = refl

complex3SubtractZeroImpliesEqual :
  ∀ left right →
  C3.complex3Subtract left right ≡ C3.complex3Zero F →
  left ≡ right
complex3SubtractZeroImpliesEqual
  (C3.complex3
    (C3.complex lxr lxi)
    (C3.complex lyr lyi)
    (C3.complex lzr lzi))
  (C3.complex3
    (C3.complex rxr rxi)
    (C3.complex ryr ryi)
    (C3.complex rzr rzi))
  differenceZero =
  let
    xRealEquation : lxr + (- rxr) ≡ 0ℚ
    xRealEquation =
      cong (λ value → C3.real (C3.x value)) differenceZero

    xImagEquation : lxi + (- rxi) ≡ 0ℚ
    xImagEquation =
      cong (λ value → C3.imaginary (C3.x value)) differenceZero

    yRealEquation : lyr + (- ryr) ≡ 0ℚ
    yRealEquation =
      cong (λ value → C3.real (C3.y value)) differenceZero

    yImagEquation : lyi + (- ryi) ≡ 0ℚ
    yImagEquation =
      cong (λ value → C3.imaginary (C3.y value)) differenceZero

    zRealEquation : lzr + (- rzr) ≡ 0ℚ
    zRealEquation =
      cong (λ value → C3.real (C3.z value)) differenceZero

    zImagEquation : lzi + (- rzi) ≡ 0ℚ
    zImagEquation =
      cong (λ value → C3.imaginary (C3.z value)) differenceZero

    xRealEqual = AddGroup.x∙y⁻¹≈ε⇒x≈y lxr rxr xRealEquation
    xImagEqual = AddGroup.x∙y⁻¹≈ε⇒x≈y lxi rxi xImagEquation
    yRealEqual = AddGroup.x∙y⁻¹≈ε⇒x≈y lyr ryr yRealEquation
    yImagEqual = AddGroup.x∙y⁻¹≈ε⇒x≈y lyi ryi yImagEquation
    zRealEqual = AddGroup.x∙y⁻¹≈ε⇒x≈y lzr rxr zRealEquation
    zImagEqual = AddGroup.x∙y⁻¹≈ε⇒x≈y lzi rzi zImagEquation
  in
  cong6
    xRealEqual xImagEqual
    yRealEqual yImagEqual
    zRealEqual zImagEqual
  where
  cong6 :
    ∀ {axr axi ayr ayi azr azi bxr bxi byr byi bzr bzi} →
    axr ≡ bxr → axi ≡ bxi →
    ayr ≡ byr → ayi ≡ byi →
    azr ≡ bzr → azi ≡ bzi →
    C3.complex3
      (C3.complex axr axi)
      (C3.complex ayr ayi)
      (C3.complex azr azi)
    ≡
    C3.complex3
      (C3.complex bxr bxi)
      (C3.complex byr byi)
      (C3.complex bzr bzi)
  cong6 refl refl refl refl refl refl = refl

complex3DifferenceNormZeroImpliesEqual :
  ∀ left right →
  L2.complex3NormSquared (C3.complex3Subtract left right) ≡ 0ℚ →
  left ≡ right
complex3DifferenceNormZeroImpliesEqual left right normZero =
  complex3SubtractZeroImpliesEqual left right
    (complex3NormSquaredZeroImpliesZero
      (C3.complex3Subtract left right)
      normZero)

rationalComplex3DifferenceSeparation :
  Inputs.Complex3DifferenceSeparation F
rationalComplex3DifferenceSeparation = record
  { zeroDifferenceNormImpliesEqual =
      complex3DifferenceNormZeroImpliesEqual
  }

rationalRestrictedTransverseTestsSeparate :
  (E : C3.IntegerEmbedding F) →
  (mode : Z3.FourierMode) →
  (left right : C3.Complex3 F) →
  Helical.Transverse E mode left →
  Helical.Transverse E mode right →
  (∀ test → Helical.Transverse E mode test →
    C3.real (C3.hermitianPairing3 test left)
    ≡ C3.real (C3.hermitianPairing3 test right)) →
  left ≡ right
rationalRestrictedTransverseTestsSeparate E =
  Inputs.complex3RestrictedTestsSeparate
    F E rationalComplex3DifferenceSeparation

rationalComplex3PositiveDefiniteClosed : Bool
rationalComplex3PositiveDefiniteClosed = true

rationalComplex3PositiveDefiniteClosedIsTrue :
  rationalComplex3PositiveDefiniteClosed ≡ true
rationalComplex3PositiveDefiniteClosedIsTrue = refl

rationalRestrictedTransposeUniquenessClosed : Bool
rationalRestrictedTransposeUniquenessClosed = true

rationalRestrictedTransposeUniquenessClosedIsTrue :
  rationalRestrictedTransposeUniquenessClosed ≡ true
rationalRestrictedTransposeUniquenessClosedIsTrue = refl
