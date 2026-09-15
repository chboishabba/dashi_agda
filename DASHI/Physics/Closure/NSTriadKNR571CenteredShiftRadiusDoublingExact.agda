module DASHI.Physics.Closure.NSTriadKNR571CenteredShiftRadiusDoublingExact where

------------------------------------------------------------------------
-- R571 GATE-A / A2 CENTERED SHIFT SCALAR RADIUS DOUBLING
--
-- Timestamp: 2026-09-15 AEST.
--
-- The centered-shift owner already proves the literal lattice identity
--
--   (k+y) + (k-y) = 2k
--
-- and the exact integer squared-norm scaling.  This owner pays the remaining
-- scalar same-object transport on the selected rational helical carrier:
--
--   modeNorm(2k) = 2 * modeNorm(k).
--
-- No square-root axiom is used.  We instead:
--   1. prove ||modeVector(2k)||^2 = 4 ||modeVector(k)||^2 by exact C3 algebra;
--   2. transport through the existing R455 radius-square calibration;
--   3. factor x^2-y^2 = (x-y)(x+y);
--   4. use rational zero-product separation and radius nonnegativity to select
--      the nonnegative root.
--
-- Ordered denominator payment and the final A2 |y|^2 curvature estimate remain
-- outside this owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Algebra.Properties.Group as GroupProperties
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as CenteredShift

module AddGroup = GroupProperties ℚP.+-0-group

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

four : ℚ
four = two * two

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

doubleVectorNormSquared :
  (value : C3.Complex3 F) →
  norm (C3.complex3Add value value) ≡ four * norm value
doubleVectorNormSquared
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex yr yi)
      (C3.complex zr zi)) =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

doubledModeNormSquaredMeaning :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (center : Z3.FourierMode) →
  C3.normSquared I (CenteredShift.doubledCenter center)
  ≡ four * C3.normSquared I center
doubledModeNormSquaredMeaning E I center =
  trans
    (sym (R96.modeVectorNormSquaredMeaning E I (CenteredShift.doubledCenter center)))
    (trans
      (cong norm (Algebra.modeVectorAdd E center center))
      (trans
        (doubleVectorNormSquared (C3.modeVector E center))
        (cong (four *_) (R96.modeVectorNormSquaredMeaning E I center))))

record CenteredShiftRadiusDoublingData
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (center : Z3.FourierMode) : Set where
  constructor centered-shift-radius-doubling-data
  field
    centerCalibration : R455.RationalModeRadiusCalibration E I S center
    doubledCalibration :
      R455.RationalModeRadiusCalibration E I S
        (CenteredShift.doubledCenter center)
    centerRadiusNonnegative : 0ℚ ≤ Helical.modeNorm S center
    doubledRadiusNonnegative :
      0ℚ ≤ Helical.modeNorm S (CenteredShift.doubledCenter center)

open CenteredShiftRadiusDoublingData public

radiusSquaresAgree :
  ∀ {E I S center} →
  (D : CenteredShiftRadiusDoublingData E I S center) →
  Helical.modeNorm S (CenteredShift.doubledCenter center)
    * Helical.modeNorm S (CenteredShift.doubledCenter center)
  ≡
  (two * Helical.modeNorm S center)
    * (two * Helical.modeNorm S center)
radiusSquaresAgree {E} {I} {S} {center} D =
  let
    r = Helical.modeNorm S center
    rd = Helical.modeNorm S (CenteredShift.doubledCenter center)
  in
  trans
    (R455.modeNormSquareMeaning (doubledCalibration D))
    (trans
      (doubledModeNormSquaredMeaning E I center)
      (trans
        (cong (four *_) (sym (R455.modeNormSquareMeaning (centerCalibration D))))
        (solve (r ∷ []))))

twoTimesNonnegative :
  ∀ {r : ℚ} → 0ℚ ≤ r → 0ℚ ≤ two * r
twoTimesNonnegative {r} rNN =
  subst
    (0ℚ ≤_)
    (sym (solve (r ∷ []) : two * r ≡ r + r))
    (Rational.addNonnegative rNN rNN)

nonnegativeEqualSquaresEqual :
  (x y : ℚ) →
  0ℚ ≤ x → 0ℚ ≤ y →
  x * x ≡ y * y →
  x ≡ y
nonnegativeEqualSquaresEqual x y xNN yNN squareEquality =
  let
    differenceOfSquaresZero : x * x - y * y ≡ 0ℚ
    differenceOfSquaresZero =
      trans
        (cong (λ value → value - y * y) squareEquality)
        (solve (y ∷ []))

    factoredZero : (x - y) * (x + y) ≡ 0ℚ
    factoredZero =
      trans
        (solve (x ∷ y ∷ []))
        differenceOfSquaresZero
  in
  case ℚP.p*q≡0⇒p≡0∨q≡0 factoredZero of λ where
    (inj₁ differenceZero) →
      AddGroup.x∙y⁻¹≈ε⇒x≈y x y differenceZero
    (inj₂ sumZero) →
      let
        zeros = Separation.nonnegativeAddZeroComponents xNN yNN sumZero
      in
      trans (proj₁ zeros) (sym (proj₂ zeros))

centeredShiftRadiusDoubles :
  ∀ {E I S center} →
  (D : CenteredShiftRadiusDoublingData E I S center) →
  Helical.modeNorm S (CenteredShift.doubledCenter center)
  ≡ two * Helical.modeNorm S center
centeredShiftRadiusDoubles {S = S} {center = center} D =
  nonnegativeEqualSquaresEqual
    (Helical.modeNorm S (CenteredShift.doubledCenter center))
    (two * Helical.modeNorm S center)
    (doubledRadiusNonnegative D)
    (twoTimesNonnegative (centerRadiusNonnegative D))
    (radiusSquaresAgree D)

r571A2CenteredShiftScalarRadiusDoublingClosed : Bool
r571A2CenteredShiftScalarRadiusDoublingClosed = true

r571A2CenteredShiftRadiusDoublingUsesR455Calibration : Bool
r571A2CenteredShiftRadiusDoublingUsesR455Calibration = true

r571A2CenteredShiftRadiusDoublingUsesSquareRootAxiom : Bool
r571A2CenteredShiftRadiusDoublingUsesSquareRootAxiom = false

r571A2OrderedRadialDenominatorPaymentClosed : Bool
r571A2OrderedRadialDenominatorPaymentClosed = false

r571A2UniformCurvatureEstimateClosed : Bool
r571A2UniformCurvatureEstimateClosed = false

r571A2ClosesR568 : Bool
r571A2ClosesR568 = false

r571A2CenteredShiftScalarRadiusDoublingClosedIsTrue :
  r571A2CenteredShiftScalarRadiusDoublingClosed ≡ true
r571A2CenteredShiftScalarRadiusDoublingClosedIsTrue = refl

r571A2CenteredShiftRadiusDoublingUsesSquareRootAxiomIsFalse :
  r571A2CenteredShiftRadiusDoublingUsesSquareRootAxiom ≡ false
r571A2CenteredShiftRadiusDoublingUsesSquareRootAxiomIsFalse = refl
