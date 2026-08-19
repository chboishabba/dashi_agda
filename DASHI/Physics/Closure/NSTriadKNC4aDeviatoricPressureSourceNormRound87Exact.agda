module DASHI.Physics.Closure.NSTriadKNC4aDeviatoricPressureSourceNormRound87Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Koji Ohkitani; Shigeo Kishiba.
-- Title: "Nonlocal nature of vortex stretching in an inviscid fluid".
-- Physics of Fluids 7 (1995), 411--421.
-- DOI: 10.1063/1.868633.
--
-- Authors: Roger A. Horn; Charles R. Johnson.
-- Title: "Matrix Analysis", Second Edition.
-- DOI: 10.1017/CBO9781139020411.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND87 / POSITIVE SAME-CONSUMER REPAIR FOR C4a
--
-- The companion Round87 no-go shows that Q and omega^T H^D omega cannot
-- determine the selected packet velocity work v^T H^D v.  The correct robust
-- replacement is norm-level control on H^D itself.
--
-- In dimension three the trace/deviatoric split is orthogonal in Frobenius
-- geometry:
--
--   ||H^D||_F^2 + (1/3) (tr H)^2 = ||H||_F^2.
--
-- Hence ||H^D||_F^2 <= ||H||_F^2.  Combining this with the already-proved
-- nine-coordinate finite Cauchy inequality gives
--
--   (v^T H^D v)^2 <= ||H||_F^2 |v|^4.
--
-- For the literal Fourier pressure Hessian, Round81/85 proves
--
--   ||H(k)||_F^2 = |(-Delta p)_k|^2,
--
-- so modewise
--
--   (v^T H^D(k) v)^2 <= |(-Delta p)_k|^2 |v|^4.
--
-- This does not yet perform the packet convolution/shell summation.  It does
-- close the local anisotropic matrix estimate without any eigenframe or Q-only
-- information loss, and identifies the one remaining C4a analytic object as a
-- pressure-source x packet-velocity convolution estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNFourierStrainFrobeniusBoundRound68Exact as Frob
import DASHI.Physics.Closure.NSTriadKNPressureEnergyOperatorDeviatoricQRound85Exact as Energy
import DASHI.Physics.Closure.NSTriadKNPressureHessianVelocityBilinearFrobeniusBoundRound85Exact as Bilinear
import DASHI.Physics.Closure.NSTriadKNPressureHessianFourierIsometryRound81Exact as P81

oneThird : ℚ
oneThird = Int.+ 1 / 3

oneThirdNonnegative : 0ℚ ≤ oneThird
oneThirdNonnegative = toWitness {a? = 0ℚ ≤? oneThird} _

tracePenalty : M.Matrix3 → ℚ
tracePenalty H = oneThird * L2.square (Energy.matrixTrace H)

tracePenaltyNonnegative : ∀ H → 0ℚ ≤ tracePenalty H
tracePenaltyNonnegative H =
  let
    squareNN = L2.squareNonnegative (Energy.matrixTrace H)
    instance
      oneThirdNNI = nonNegative oneThirdNonnegative
      squareNNI = nonNegative squareNN
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg oneThird (L2.square (Energy.matrixTrace H))
  in
  ℚP.nonNegative⁻¹ (tracePenalty H)

deviatoricFrobeniusPythagoras : ∀ H →
  Frob.frobeniusSquared (Energy.deviatoric H)
    + tracePenalty H
  ≡ Frob.frobeniusSquared H
deviatoricFrobeniusPythagoras
    (M.matrix3 h11 h12 h13 h21 h22 h23 h31 h32 h33) =
  solve
    (h11 ∷ h12 ∷ h13 ∷ h21 ∷ h22 ∷ h23 ∷ h31 ∷ h32 ∷ h33 ∷ [])

deviatoricFrobeniusDominatedByFull : ∀ H →
  Frob.frobeniusSquared (Energy.deviatoric H)
  ≤ Frob.frobeniusSquared H
deviatoricFrobeniusDominatedByFull H =
  let
    dev = Frob.frobeniusSquared (Energy.deviatoric H)
    penalty = tracePenalty H
    added : dev + 0ℚ ≤ dev + penalty
    added = ℚP.+-monoˡ-≤ dev (tracePenaltyNonnegative H)
    fromZero : dev ≤ dev + penalty
    fromZero = subst (λ left → left ≤ dev + penalty) (solve (dev ∷ [])) added
  in
  subst (λ right → dev ≤ right) (deviatoricFrobeniusPythagoras H) fromZero

vectorNormSquaredNonnegative : ∀ v → 0ℚ ≤ V.normSquared v
vectorNormSquaredNonnegative (V.v3 x y z) =
  L2.addNonnegative
    (L2.addNonnegative (L2.squareNonnegative x) (L2.squareNonnegative y))
    (L2.squareNonnegative z)

vectorNormFourthNonnegative : ∀ v →
  0ℚ ≤ V.normSquared v * V.normSquared v
vectorNormFourthNonnegative v =
  let
    normNN = vectorNormSquaredNonnegative v
    instance
      leftNN = nonNegative normNN
      rightNN = nonNegative normNN
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg (V.normSquared v) (V.normSquared v)
  in
  ℚP.nonNegative⁻¹ (V.normSquared v * V.normSquared v)

deviatoricVelocityWorkSquaredBoundByFullFrobenius : ∀ H v →
  L2.square (Bilinear.velocityHessianWork (Energy.deviatoric H) v v)
  ≤ Frob.frobeniusSquared H *
      (V.normSquared v * V.normSquared v)
deviatoricVelocityWorkSquaredBoundByFullFrobenius H v =
  let
    local = Bilinear.velocityHessianWorkSquaredBound (Energy.deviatoric H) v v
    norm4 = V.normSquared v * V.normSquared v
    instance norm4NN = nonNegative (vectorNormFourthNonnegative v)
    scaled = ℚP.*-monoʳ-≤-nonNeg norm4 (deviatoricFrobeniusDominatedByFull H)
  in
  ℚP.≤-trans local scaled

deviatoricPressureHessianMode : P81.NonzeroModePoissonMultiplier → M.Matrix3
deviatoricPressureHessianMode datum =
  Energy.deviatoric (Bilinear.pressureHessianMatrix datum)

pressureDeviatoricVelocityWorkSourceBound : ∀ datum v →
  L2.square
    (Bilinear.velocityHessianWork
      (deviatoricPressureHessianMode datum) v v)
  ≤ P81.square (P81.sourceCoefficient datum) *
      (V.normSquared v * V.normSquared v)
pressureDeviatoricVelocityWorkSourceBound datum v =
  subst
    (λ coefficient →
      L2.square
        (Bilinear.velocityHessianWork
          (deviatoricPressureHessianMode datum) v v)
      ≤ coefficient * (V.normSquared v * V.normSquared v))
    (Bilinear.pressureHessianMatrixFrobeniusIsSourceSquare datum)
    (deviatoricVelocityWorkSquaredBoundByFullFrobenius
      (Bilinear.pressureHessianMatrix datum) v)

round87DeviatoricFrobeniusOrthogonalTraceSplitConstructed : Bool
round87DeviatoricFrobeniusOrthogonalTraceSplitConstructed = true

round87DeviatoricVelocityWorkControlledByPressureSourceModewise : Bool
round87DeviatoricVelocityWorkControlledByPressureSourceModewise = true

round87SelectedPacketDeviatoricPressureConvolutionBoundConstructed : Bool
round87SelectedPacketDeviatoricPressureConvolutionBoundConstructed = false

round87DeviatoricVelocityWorkControlledByPressureSourceModewiseIsTrue :
  round87DeviatoricVelocityWorkControlledByPressureSourceModewise ≡ true
round87DeviatoricVelocityWorkControlledByPressureSourceModewiseIsTrue = refl

round87SelectedPacketDeviatoricPressureConvolutionBoundConstructedIsFalse :
  round87SelectedPacketDeviatoricPressureConvolutionBoundConstructed ≡ false
round87SelectedPacketDeviatoricPressureConvolutionBoundConstructedIsFalse = refl
