{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345UnitGeometryRound842Exact where

------------------------------------------------------------------------
-- R842 / UNIT-NORMALIZED RATIONAL GEOMETRY FOR THE ACTIVE 3-4-5 MODES
--
-- The R828 component certificate uses the ordinary integer Fourier embedding.
-- Rather than assume eight unrelated inverse-square numbers, derive them from:
--
--   E(1)=1,
--   C3.normSquaredMeaning,
--   C3.inverseLaw.
--
-- Thus every active Leray projector used by R829 has the exact rational
-- geometry 1/9, 1/16, or 1/25 required by the component calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

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
k₁Nonzero = record { notZero = λ () }

k₂Nonzero : Z3.NonZeroMode Active.k₂
k₂Nonzero = record { notZero = λ () }

k₃Nonzero : Z3.NonZeroMode Active.k₃
k₃Nonzero = record { notZero = λ () }

k₄Nonzero : Z3.NonZeroMode Active.k₄
k₄Nonzero = record { notZero = λ () }

k₅Nonzero : Z3.NonZeroMode Active.k₅
k₅Nonzero = record { notZero = λ () }

k₆Nonzero : Z3.NonZeroMode Active.k₆
k₆Nonzero = record { notZero = λ () }

k₇Nonzero : Z3.NonZeroMode Active.k₇
k₇Nonzero = record { notZero = λ () }

k₈Nonzero : Z3.NonZeroMode Active.k₈
k₈Nonzero = record { notZero = λ () }

record Unit345Geometry
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set where
  constructor unit-345-geometry
  field
    unitEmbedding : Unit.UnitPreservingIntegerEmbedding F E

open Unit345Geometry public

normSquaredExact :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Unit345Geometry E I →
  (mode : Z3.FourierMode) →
  C3.normSquared I mode ≡ Lattice.latticeSquaredDisplacement mode
normSquaredExact G mode =
  UnitWeld.liveSquaredDisplacementIsLattice
    (unitEmbedding G) _ mode

norm₁ : Lattice.latticeSquaredDisplacement Active.k₁ ≡ 25
norm₁ = refl
norm₂ : Lattice.latticeSquaredDisplacement Active.k₂ ≡ 9
norm₂ = refl
norm₃ : Lattice.latticeSquaredDisplacement Active.k₃ ≡ 25
norm₃ = refl
norm₄ : Lattice.latticeSquaredDisplacement Active.k₄ ≡ 16
norm₄ = refl
norm₅ : Lattice.latticeSquaredDisplacement Active.k₅ ≡ 16
norm₅ = refl
norm₆ : Lattice.latticeSquaredDisplacement Active.k₆ ≡ 25
norm₆ = refl
norm₇ : Lattice.latticeSquaredDisplacement Active.k₇ ≡ 9
norm₇ = refl
norm₈ : Lattice.latticeSquaredDisplacement Active.k₈ ≡ 25
norm₈ = refl

inverseFromNorm :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (mode : Z3.FourierMode)
    (nonzero : Z3.NonZeroMode mode)
    (n : ℚ) →
  C3.normSquared I mode ≡ n →
  C3.inverseNormSquared I mode * n ≡ 1ℚ
inverseFromNorm {I = I} mode nonzero n norm =
  trans
    (cong (C3.inverseNormSquared I mode *_) (sym norm))
    (C3.inverseLaw I mode nonzero)

inverse₁ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (G : Unit345Geometry E I) →
  C3.inverseNormSquared I Active.k₁ ≡ (+ 1) / 25
inverse₁ {I = I} G =
  let h =
    inverseFromNorm Active.k₁ k₁Nonzero 25
      (trans (normSquaredExact G Active.k₁) norm₁)
  in solve (C3.inverseNormSquared I Active.k₁ ∷ []) h

inverse₂ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (G : Unit345Geometry E I) →
  C3.inverseNormSquared I Active.k₂ ≡ (+ 1) / 9
inverse₂ {I = I} G =
  let h =
    inverseFromNorm Active.k₂ k₂Nonzero 9
      (trans (normSquaredExact G Active.k₂) norm₂)
  in solve (C3.inverseNormSquared I Active.k₂ ∷ []) h

inverse₃ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (G : Unit345Geometry E I) →
  C3.inverseNormSquared I Active.k₃ ≡ (+ 1) / 25
inverse₃ {I = I} G =
  let h =
    inverseFromNorm Active.k₃ k₃Nonzero 25
      (trans (normSquaredExact G Active.k₃) norm₃)
  in solve (C3.inverseNormSquared I Active.k₃ ∷ []) h

inverse₄ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (G : Unit345Geometry E I) →
  C3.inverseNormSquared I Active.k₄ ≡ (+ 1) / 16
inverse₄ {I = I} G =
  let h =
    inverseFromNorm Active.k₄ k₄Nonzero 16
      (trans (normSquaredExact G Active.k₄) norm₄)
  in solve (C3.inverseNormSquared I Active.k₄ ∷ []) h

inverse₅ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (G : Unit345Geometry E I) →
  C3.inverseNormSquared I Active.k₅ ≡ (+ 1) / 16
inverse₅ {I = I} G =
  let h =
    inverseFromNorm Active.k₅ k₅Nonzero 16
      (trans (normSquaredExact G Active.k₅) norm₅)
  in solve (C3.inverseNormSquared I Active.k₅ ∷ []) h

inverse₆ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (G : Unit345Geometry E I) →
  C3.inverseNormSquared I Active.k₆ ≡ (+ 1) / 25
inverse₆ {I = I} G =
  let h =
    inverseFromNorm Active.k₆ k₆Nonzero 25
      (trans (normSquaredExact G Active.k₆) norm₆)
  in solve (C3.inverseNormSquared I Active.k₆ ∷ []) h

inverse₇ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (G : Unit345Geometry E I) →
  C3.inverseNormSquared I Active.k₇ ≡ (+ 1) / 9
inverse₇ {I = I} G =
  let h =
    inverseFromNorm Active.k₇ k₇Nonzero 9
      (trans (normSquaredExact G Active.k₇) norm₇)
  in solve (C3.inverseNormSquared I Active.k₇ ∷ []) h

inverse₈ :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (G : Unit345Geometry E I) →
  C3.inverseNormSquared I Active.k₈ ≡ (+ 1) / 25
inverse₈ {I = I} G =
  let h =
    inverseFromNorm Active.k₈ k₈Nonzero 25
      (trans (normSquaredExact G Active.k₈) norm₈)
  in solve (C3.inverseNormSquared I Active.k₈ ∷ []) h

round842ActiveNormSquaresExact : Bool
round842ActiveNormSquaresExact = true

round842ActiveInverseSquaresDerived : Bool
round842ActiveInverseSquaresDerived = true

round842IndependentInverseSquareAssumptionsRequired : Bool
round842IndependentInverseSquareAssumptionsRequired = false

round842ClayPromotion : Bool
round842ClayPromotion = false

round842ActiveInverseSquaresDerivedIsTrue :
  round842ActiveInverseSquaresDerived ≡ true
round842ActiveInverseSquaresDerivedIsTrue = refl
