module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramFiniteRangeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Jean-Michel Combes; Lawrence Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Compose the literal selected-background gauge matrix with its transpose and
-- prove finite range from the actual row stencil.  Two gauge rows with no
-- common supported state coordinate have exactly zero Gram entry.  This is a
-- structural equality before a Combes--Thomas norm estimate and closes the
-- gauge-only part of the constraint-Gram finite-range producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (0ℚ; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintStencilExact as Stencil

selectedBackgroundGaugeGram :
  Physical.RationalSU2Background4 →
  Rect.RectangularMatrix
    FlatGauge.GaugeCoordinate4 FlatGauge.GaugeCoordinate4
selectedBackgroundGaugeGram background =
  Rect.composeRectangular KKT.physicalStateCarrier
    (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background)
    (Rect.transposeRectangular
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background))

data GaugeRowsSeparatedAt
    (left right : FlatGauge.GaugeCoordinate4)
    (column : KKT.State) : Set where
  leftRowOutside :
    (Stencil.GaugeConstraintSpatialSupport left column → ⊥) →
    GaugeRowsSeparatedAt left right column

  rightRowOutside :
    (Stencil.GaugeConstraintSpatialSupport right column → ⊥) →
    GaugeRowsSeparatedAt left right column

record GaugeRowsHaveDisjointStencils
    (left right : FlatGauge.GaugeCoordinate4) : Set where
  field
    separatedAt : ∀ column → GaugeRowsSeparatedAt left right column
open GaugeRowsHaveDisjointStencils public

gaugeGramTermZeroWhenSeparated :
  ∀ background left right column →
  GaugeRowsSeparatedAt left right column →
  GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
      background left column
    * GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
        background right column
  ≡ 0ℚ
gaugeGramTermZeroWhenSeparated
    background left right column (leftRowOutside outside)
  rewrite Stencil.selectedBackgroundGaugeConstraintMatrixOutsideStencilZero
      background left column outside =
  ℚRing.solve-∀
    (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
      background right column)
gaugeGramTermZeroWhenSeparated
    background left right column (rightRowOutside outside)
  rewrite Stencil.selectedBackgroundGaugeConstraintMatrixOutsideStencilZero
      background right column outside =
  ℚRing.solve-∀
    (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
      background left column)

selectedBackgroundGaugeGramOutsideRangeZero :
  ∀ background left right →
  GaugeRowsHaveDisjointStencils left right →
  selectedBackgroundGaugeGram background left right ≡ 0ℚ
selectedBackgroundGaugeGramOutsideRangeZero
    background left right separation =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates KKT.physicalStateCarrier)
      (λ column →
        GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          background left column
        * GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          background right column)
      (λ _ → 0ℚ)
      (λ column →
        gaugeGramTermZeroWhenSeparated
          background left right column
          (separatedAt separation column)))
    (Fubini.sumRationalZero
      (Matrix.coordinates KKT.physicalStateCarrier))

selectedGaugeGramFiniteRangeLevel : ProofLevel
selectedGaugeGramFiniteRangeLevel = machineChecked
