{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109MixedLorentzFourierVanishingExact where

------------------------------------------------------------------------
-- ROW A GAUSSIAN WELD: POSITION-SPACE LORENTZ DIAGONALITY SURVIVES FOURIER
--
-- The parallel Lean lane proves that the block-averaging variation and the
-- constrained projection variation are Lorentz block diagonal in position
-- space, and that the lattice Fourier transform acts only on position indices.
-- Consequently every mixed Lorentz component of those two variations is zero in
-- momentum space as well.
--
-- This file proves the algebraic statement independently in Agda.  No analytic
-- estimate is involved: a Fourier component is a finite weighted sum over
-- position, and a weighted sum of identically-zero mixed components is zero.
-- Therefore, on the selected mixed component,
--
--             Q_mixed = 0,     R_mixed = 0,
--             (W + Q + R)_mixed = W_mixed.
--
-- The remaining physical source work is only same-object identification of the
-- literal CMP98/CMP99 variations with the position-space diagonal carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record FourierScalarAlgebra (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    _+_ : Scalar → Scalar → Scalar
    _*_ : Scalar → Scalar → Scalar
    zeroPlus : ∀ x → zero + x ≡ x
    plusZero : ∀ x → x + zero ≡ x
    timesZero : ∀ x → x * zero ≡ zero

open FourierScalarAlgebra public

weightedPositionSum :
  ∀ {Position Momentum Lorentz Scalar}
    (alg : FourierScalarAlgebra Scalar) →
    List Position →
    (Momentum → Position → Scalar) →
    (Position → Lorentz → Lorentz → Scalar) →
    Momentum → Lorentz → Lorentz → Scalar
weightedPositionSum alg [] coefficient value momentum μ ν = zero alg
weightedPositionSum alg (position ∷ rest) coefficient value momentum μ ν =
  _+_ alg
    (_*_ alg (coefficient momentum position) (value position μ ν))
    (weightedPositionSum alg rest coefficient value momentum μ ν)

weightedPositionSumOfMixedZerosIsZero :
  ∀ {Position Momentum Lorentz Scalar}
    (alg : FourierScalarAlgebra Scalar)
    (positions : List Position)
    (coefficient : Momentum → Position → Scalar)
    (value : Position → Lorentz → Lorentz → Scalar)
    (momentum : Momentum) (μ ν : Lorentz) →
    (∀ position → value position μ ν ≡ zero alg) →
  weightedPositionSum alg positions coefficient value momentum μ ν
  ≡ zero alg
weightedPositionSumOfMixedZerosIsZero alg [] coefficient value momentum μ ν mixedZero = refl
weightedPositionSumOfMixedZerosIsZero alg (position ∷ rest) coefficient value momentum μ ν mixedZero =
  trans
    (cong₂ (_+_ alg)
      (trans
        (cong (_*_ alg (coefficient momentum position)) (mixedZero position))
        (timesZero alg (coefficient momentum position)))
      (weightedPositionSumOfMixedZerosIsZero
        alg rest coefficient value momentum μ ν mixedZero))
    (zeroPlus alg (zero alg))

record LorentzDiagonalPositionVariation
    (Position Momentum Lorentz Scalar : Set)
    (alg : FourierScalarAlgebra Scalar) : Set₁ where
  field
    positions : List Position
    fourierCoefficient : Momentum → Position → Scalar
    positionVariation : Position → Lorentz → Lorentz → Scalar

    OffDiagonal : Lorentz → Lorentz → Set
    positionMixedZero : ∀ μ ν → OffDiagonal μ ν → ∀ position →
      positionVariation position μ ν ≡ zero alg

open LorentzDiagonalPositionVariation public

fourierVariation :
  ∀ {Position Momentum Lorentz Scalar}
    {alg : FourierScalarAlgebra Scalar} →
  LorentzDiagonalPositionVariation Position Momentum Lorentz Scalar alg →
  Momentum → Lorentz → Lorentz → Scalar
fourierVariation {alg = alg} dataSet =
  weightedPositionSum alg
    (positions dataSet)
    (fourierCoefficient dataSet)
    (positionVariation dataSet)

fourierMixedZero :
  ∀ {Position Momentum Lorentz Scalar}
    {alg : FourierScalarAlgebra Scalar}
    (dataSet : LorentzDiagonalPositionVariation
      Position Momentum Lorentz Scalar alg)
    momentum μ ν → OffDiagonal dataSet μ ν →
  fourierVariation dataSet momentum μ ν ≡ zero alg
fourierMixedZero {alg = alg} dataSet momentum μ ν offDiagonal =
  weightedPositionSumOfMixedZerosIsZero
    alg
    (positions dataSet)
    (fourierCoefficient dataSet)
    (positionVariation dataSet)
    momentum μ ν
    (positionMixedZero dataSet μ ν offDiagonal)

------------------------------------------------------------------------
-- W + Q + R simplification on a selected mixed Lorentz component.
------------------------------------------------------------------------

record MixedWQRCarrier
    (Position Momentum Lorentz Scalar : Set)
    (alg : FourierScalarAlgebra Scalar) : Set₁ where
  field
    wilsonMixed : Momentum → Lorentz → Lorentz → Scalar
    averagingVariation :
      LorentzDiagonalPositionVariation Position Momentum Lorentz Scalar alg
    constrainedVariation :
      LorentzDiagonalPositionVariation Position Momentum Lorentz Scalar alg

    sameOffDiagonal : ∀ μ ν →
      OffDiagonal averagingVariation μ ν →
      OffDiagonal constrainedVariation μ ν

open MixedWQRCarrier public

mixedWQR :
  ∀ {Position Momentum Lorentz Scalar}
    {alg : FourierScalarAlgebra Scalar} →
  MixedWQRCarrier Position Momentum Lorentz Scalar alg →
  Momentum → Lorentz → Lorentz → Scalar
mixedWQR {alg = alg} dataSet momentum μ ν =
  _+_ alg
    (_+_ alg
      (wilsonMixed dataSet momentum μ ν)
      (fourierVariation (averagingVariation dataSet) momentum μ ν))
    (fourierVariation (constrainedVariation dataSet) momentum μ ν)

mixedWQREqualsWilson :
  ∀ {Position Momentum Lorentz Scalar}
    {alg : FourierScalarAlgebra Scalar}
    (dataSet : MixedWQRCarrier Position Momentum Lorentz Scalar alg)
    momentum μ ν
    (offDiagonal : OffDiagonal (averagingVariation dataSet) μ ν) →
  mixedWQR dataSet momentum μ ν ≡ wilsonMixed dataSet momentum μ ν
mixedWQREqualsWilson {alg = alg} dataSet momentum μ ν offDiagonal =
  let
    qZero = fourierMixedZero
      (averagingVariation dataSet) momentum μ ν offDiagonal
    rZero = fourierMixedZero
      (constrainedVariation dataSet) momentum μ ν
      (sameOffDiagonal dataSet μ ν offDiagonal)
  in
  trans
    (cong₂ (_+_ alg)
      (cong₂ (_+_ alg) refl qZero)
      rZero)
    (trans
      (cong (λ value → _+_ alg value (zero alg))
        (plusZero alg (wilsonMixed dataSet momentum μ ν)))
      (plusZero alg (wilsonMixed dataSet momentum μ ν)))

mixedLorentzFourierVanishingLevel : ProofLevel
mixedLorentzFourierVanishingLevel = machineChecked

mixedWQREqualsWilsonLevel : ProofLevel
mixedWQREqualsWilsonLevel = machineChecked

-- Physical source seam: identify CMP98 DQ and the constrained part of CMP99 DR
-- with the position-space Lorentz-diagonal variations above, with the same
-- Fourier convention used by the CMP109 Gaussian trace.  Once that lands, Q/R
-- do not consume any mixed-component patch margin.
literalCMP98AveragingLorentzDiagonalIdentificationLevel : ProofLevel
literalCMP98AveragingLorentzDiagonalIdentificationLevel = conditional

literalCMP99ConstrainedProjectionLorentzDiagonalIdentificationLevel : ProofLevel
literalCMP99ConstrainedProjectionLorentzDiagonalIdentificationLevel = conditional
