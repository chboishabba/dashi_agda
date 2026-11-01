module DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact where

------------------------------------------------------------------------
-- ROUND455 / RATIONAL SCALAR RADIUS CALIBRATION -> UNIT NORMALIZED DIRECTION
--
-- R96 already owns the literal rational identity
--
--   ||modeVector(k)||^2 = normSquared(k).
--
-- R167 defines
--
--   normalizedDirection(k) = inverseModeNorm(k) * modeVector(k).
--
-- Therefore the only scalar representation facts needed to prove unit norm are
--
--   modeNorm(k)^2 = normSquared(k),
--   modeNorm(k) * inverseModeNorm(k) = 1.
--
-- This owner packages exactly those same-object receipts and proves
--
--   ||normalizedDirection(k)||^2 = 1
--
-- on the literal rational C^3 carrier.  No square root, scalar cancellation
-- from a vector equation, or new analytic estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96

F : C3.RealField _
F = Rational.rationalRealField

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

record RationalModeRadiusCalibration
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (mode : Z3.FourierMode) : Set where
  constructor rational-mode-radius-calibration
  field
    modeNormSquareMeaning :
      Helical.modeNorm S mode * Helical.modeNorm S mode
      ≡ C3.normSquared I mode

    modeNormInverseLaw :
      Helical.modeNorm S mode * Helical.inverseModeNorm S mode ≡ 1ℚ

open RationalModeRadiusCalibration public

record ExplicitRadiusWitness
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (mode : Z3.FourierMode) : Set where
  constructor explicit-radius-witness
  field
    radius inverse : ℚ
    radiusMeaning : radius ≡ Helical.modeNorm S mode
    inverseMeaning : inverse ≡ Helical.inverseModeNorm S mode
    radiusSquareMeaning : radius * radius ≡ C3.normSquared I mode
    radiusInverseLaw : radius * inverse ≡ 1ℚ

open ExplicitRadiusWitness public

explicitWitnessToCalibration :
  ∀ {E I S mode} →
  ExplicitRadiusWitness E I S mode →
  RationalModeRadiusCalibration E I S mode
explicitWitnessToCalibration W =
  rational-mode-radius-calibration
    (trans
      (cong₂ _*_
        (sym (radiusMeaning W))
        (sym (radiusMeaning W)))
      (radiusSquareMeaning W))
    (trans
      (cong₂ _*_
        (sym (radiusMeaning W))
        (sym (inverseMeaning W)))
      (radiusInverseLaw W))

realEmbedModulusSquared :
  (x : ℚ) →
  L2.complexModulusSquared (C3.realEmbed F x) ≡ x * x
realEmbedModulusSquared x = solve (x ∷ [])

normalizedDirectionNormExpanded :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F)
  (mode : Z3.FourierMode) →
  norm (R167.normalizedDirection E S mode)
  ≡
  (Helical.inverseModeNorm S mode * Helical.inverseModeNorm S mode)
    * C3.normSquared I mode
normalizedDirectionNormExpanded E I S mode =
  trans
    (R174.normScale
      (C3.realEmbed F (Helical.inverseModeNorm S mode))
      (C3.modeVector E mode))
    (trans
      (cong₂ _*_
        (realEmbedModulusSquared (Helical.inverseModeNorm S mode))
        refl)
      (cong
        ((Helical.inverseModeNorm S mode * Helical.inverseModeNorm S mode) *_)
        (R96.modeVectorNormSquaredMeaning E I mode)))

normalizedDirectionUnit :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F)
  (mode : Z3.FourierMode) →
  RationalModeRadiusCalibration E I S mode →
  norm (R167.normalizedDirection E S mode) ≡ 1ℚ
normalizedDirectionUnit E I S mode C =
  let
    radius = Helical.modeNorm S mode
    inverse = Helical.inverseModeNorm S mode
    normSquare = C3.normSquared I mode

    expanded = normalizedDirectionNormExpanded E I S mode

    replaceNormSquare :
      (inverse * inverse) * normSquare
      ≡ (inverse * inverse) * (radius * radius)
    replaceNormSquare =
      cong ((inverse * inverse) *_)
        (sym (modeNormSquareMeaning C))

    regroup :
      (inverse * inverse) * (radius * radius)
      ≡ (radius * inverse) * (radius * inverse)
    regroup = solve (radius ∷ inverse ∷ [])

    cancel :
      (radius * inverse) * (radius * inverse) ≡ 1ℚ
    cancel =
      trans
        (cong₂ _*_
          (modeNormInverseLaw C)
          (modeNormInverseLaw C))
        (solve [])
  in
  trans expanded (trans replaceNormSquare (trans regroup cancel))

round455RationalModeVectorNormMeaningReused : Bool
round455RationalModeVectorNormMeaningReused = true

round455ScalarRadiusCalibrationImpliesUnitDirection : Bool
round455ScalarRadiusCalibrationImpliesUnitDirection = true

round455VectorScalarCancellationUsed : Bool
round455VectorScalarCancellationUsed = false

round455SquareRootUsed : Bool
round455SquareRootUsed = false

round455PackageAClosed : Bool
round455PackageAClosed = false

round455ClayPromotion : Bool
round455ClayPromotion = false

round455VectorScalarCancellationUsedIsFalse :
  round455VectorScalarCancellationUsed ≡ false
round455VectorScalarCancellationUsedIsFalse = refl

round455SquareRootUsedIsFalse : round455SquareRootUsed ≡ false
round455SquareRootUsedIsFalse = refl
