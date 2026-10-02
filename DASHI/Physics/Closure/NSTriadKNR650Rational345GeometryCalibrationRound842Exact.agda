{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345GeometryCalibrationRound842Exact where

------------------------------------------------------------------------
-- R842 / UNIT-NORMALIZED EXACT FOURIER GEOMETRY FOR THE ACTIVE 3-4-5 MODES
--
-- Under the repository's explicit UnitPreservingIntegerEmbedding hypothesis,
-- R571 proves
--
--     normSquared_I(k) = |k|_Z^2.
--
-- On the eight active R829 modes these squares are exactly 25,9,25,16,16,25,9,25.
-- ModeInverseSquare.inverseLaw therefore forces the active Leray reciprocals
-- to be 1/25,1/9,1/25,1/16,1/16,1/25,1/9,1/25.
--
-- Thus R829 does not need an additional freely supplied geometry calibration.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR571UnitNormalizedDisplacementWeldExact as UnitWeld
import DASHI.Physics.Closure.NSTriadKNR571LatticeDisplacementG2Exact as Lattice
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active

F : C3.RealField _
F = Rational.rationalRealField

k₁Nonzero : Z3.NonZeroMode Active.k₁
k₁Nonzero = record { Z3.notZero = λ () }
k₂Nonzero : Z3.NonZeroMode Active.k₂
k₂Nonzero = record { Z3.notZero = λ () }
k₃Nonzero : Z3.NonZeroMode Active.k₃
k₃Nonzero = record { Z3.notZero = λ () }
k₄Nonzero : Z3.NonZeroMode Active.k₄
k₄Nonzero = record { Z3.notZero = λ () }
k₅Nonzero : Z3.NonZeroMode Active.k₅
k₅Nonzero = record { Z3.notZero = λ () }
k₆Nonzero : Z3.NonZeroMode Active.k₆
k₆Nonzero = record { Z3.notZero = λ () }
k₇Nonzero : Z3.NonZeroMode Active.k₇
k₇Nonzero = record { Z3.notZero = λ () }
k₈Nonzero : Z3.NonZeroMode Active.k₈
k₈Nonzero = record { Z3.notZero = λ () }

lattice₁ : Lattice.latticeSquaredDisplacement Active.k₁ ≡ 25
lattice₁ = refl
lattice₂ : Lattice.latticeSquaredDisplacement Active.k₂ ≡ 9
lattice₂ = refl
lattice₃ : Lattice.latticeSquaredDisplacement Active.k₃ ≡ 25
lattice₃ = refl
lattice₄ : Lattice.latticeSquaredDisplacement Active.k₄ ≡ 16
lattice₄ = refl
lattice₅ : Lattice.latticeSquaredDisplacement Active.k₅ ≡ 16
lattice₅ = refl
lattice₆ : Lattice.latticeSquaredDisplacement Active.k₆ ≡ 25
lattice₆ = refl
lattice₇ : Lattice.latticeSquaredDisplacement Active.k₇ ≡ 9
lattice₇ = refl
lattice₈ : Lattice.latticeSquaredDisplacement Active.k₈ ≡ 25
lattice₈ = refl

module Geometry
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  norm₁ : C3.normSquared I Active.k₁ ≡ 25
  norm₁ = trans (UnitWeld.liveSquaredDisplacementIsLattice unit I Active.k₁) lattice₁
  norm₂ : C3.normSquared I Active.k₂ ≡ 9
  norm₂ = trans (UnitWeld.liveSquaredDisplacementIsLattice unit I Active.k₂) lattice₂
  norm₃ : C3.normSquared I Active.k₃ ≡ 25
  norm₃ = trans (UnitWeld.liveSquaredDisplacementIsLattice unit I Active.k₃) lattice₃
  norm₄ : C3.normSquared I Active.k₄ ≡ 16
  norm₄ = trans (UnitWeld.liveSquaredDisplacementIsLattice unit I Active.k₄) lattice₄
  norm₅ : C3.normSquared I Active.k₅ ≡ 16
  norm₅ = trans (UnitWeld.liveSquaredDisplacementIsLattice unit I Active.k₅) lattice₅
  norm₆ : C3.normSquared I Active.k₆ ≡ 25
  norm₆ = trans (UnitWeld.liveSquaredDisplacementIsLattice unit I Active.k₆) lattice₆
  norm₇ : C3.normSquared I Active.k₇ ≡ 9
  norm₇ = trans (UnitWeld.liveSquaredDisplacementIsLattice unit I Active.k₇) lattice₇
  norm₈ : C3.normSquared I Active.k₈ ≡ 25
  norm₈ = trans (UnitWeld.liveSquaredDisplacementIsLattice unit I Active.k₈) lattice₈

  reciprocal25 :
    (x : ℚ) → x * 25 ≡ 1ℚ → x ≡ (+ 1) / 25
  reciprocal25 x law =
    trans
      (solve (x ∷ []))
      (trans
        (cong (((+ 1) / 25) *_) law)
        (solve []))

  reciprocal16 :
    (x : ℚ) → x * 16 ≡ 1ℚ → x ≡ (+ 1) / 16
  reciprocal16 x law =
    trans
      (solve (x ∷ []))
      (trans
        (cong (((+ 1) / 16) *_) law)
        (solve []))

  reciprocal9 :
    (x : ℚ) → x * 9 ≡ 1ℚ → x ≡ (+ 1) / 9
  reciprocal9 x law =
    trans
      (solve (x ∷ []))
      (trans
        (cong (((+ 1) / 9) *_) law)
        (solve []))

  inv₁ : C3.inverseNormSquared I Active.k₁ ≡ (+ 1) / 25
  inv₁ =
    reciprocal25 (C3.inverseNormSquared I Active.k₁)
      (subst
        (λ n → C3.inverseNormSquared I Active.k₁ * n ≡ 1ℚ)
        norm₁
        (C3.inverseLaw I Active.k₁ k₁Nonzero))

  inv₂ : C3.inverseNormSquared I Active.k₂ ≡ (+ 1) / 9
  inv₂ =
    reciprocal9 (C3.inverseNormSquared I Active.k₂)
      (subst
        (λ n → C3.inverseNormSquared I Active.k₂ * n ≡ 1ℚ)
        norm₂
        (C3.inverseLaw I Active.k₂ k₂Nonzero))

  inv₃ : C3.inverseNormSquared I Active.k₃ ≡ (+ 1) / 25
  inv₃ =
    reciprocal25 (C3.inverseNormSquared I Active.k₃)
      (subst
        (λ n → C3.inverseNormSquared I Active.k₃ * n ≡ 1ℚ)
        norm₃
        (C3.inverseLaw I Active.k₃ k₃Nonzero))

  inv₄ : C3.inverseNormSquared I Active.k₄ ≡ (+ 1) / 16
  inv₄ =
    reciprocal16 (C3.inverseNormSquared I Active.k₄)
      (subst
        (λ n → C3.inverseNormSquared I Active.k₄ * n ≡ 1ℚ)
        norm₄
        (C3.inverseLaw I Active.k₄ k₄Nonzero))

  inv₅ : C3.inverseNormSquared I Active.k₅ ≡ (+ 1) / 16
  inv₅ =
    reciprocal16 (C3.inverseNormSquared I Active.k₅)
      (subst
        (λ n → C3.inverseNormSquared I Active.k₅ * n ≡ 1ℚ)
        norm₅
        (C3.inverseLaw I Active.k₅ k₅Nonzero))

  inv₆ : C3.inverseNormSquared I Active.k₆ ≡ (+ 1) / 25
  inv₆ =
    reciprocal25 (C3.inverseNormSquared I Active.k₆)
      (subst
        (λ n → C3.inverseNormSquared I Active.k₆ * n ≡ 1ℚ)
        norm₆
        (C3.inverseLaw I Active.k₆ k₆Nonzero))

  inv₇ : C3.inverseNormSquared I Active.k₇ ≡ (+ 1) / 9
  inv₇ =
    reciprocal9 (C3.inverseNormSquared I Active.k₇)
      (subst
        (λ n → C3.inverseNormSquared I Active.k₇ * n ≡ 1ℚ)
        norm₇
        (C3.inverseLaw I Active.k₇ k₇Nonzero))

  inv₈ : C3.inverseNormSquared I Active.k₈ ≡ (+ 1) / 25
  inv₈ =
    reciprocal25 (C3.inverseNormSquared I Active.k₈)
      (subst
        (λ n → C3.inverseNormSquared I Active.k₈ * n ≡ 1ℚ)
        norm₈
        (C3.inverseLaw I Active.k₈ k₈Nonzero))

round842ActiveNormSquaresForcedByUnitNormalization : Bool
round842ActiveNormSquaresForcedByUnitNormalization = true

round842ActiveInverseSquaresForcedByInverseLaw : Bool
round842ActiveInverseSquaresForcedByInverseLaw = true

round842AdditionalGeometryCalibrationLeafRequired : Bool
round842AdditionalGeometryCalibrationLeafRequired = false

round842ClayPromotion : Bool
round842ClayPromotion = false

round842AdditionalGeometryCalibrationLeafRequiredIsFalse :
  round842AdditionalGeometryCalibrationLeafRequired ≡ false
round842AdditionalGeometryCalibrationLeafRequiredIsFalse = refl
