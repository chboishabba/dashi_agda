{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345R30OrderedCellsRound843Exact where

------------------------------------------------------------------------
-- R843 / THE SIXTEEN EXACT ORDERED R30 CELLS OF THE 3-4-5 SNAPSHOT
--
-- After R840 sparse pruning, the selected radius-four nonlinearity has only
-- sixteen nonzero ordered seed-pair interactions: two for each active output.
-- R842 fixes all wave-vector and Leray geometry under the repository's ordinary
-- unit-preserving Fourier normalization.  This owner evaluates those sixteen
-- literal Audit.projectedOrderedTerm values by exact rational ring arithmetic.
--
-- No Python value is imported as an axiom: the target vectors below are
-- ordinary C^3(Q) literals and each theorem reduces the repository R30 formula.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _/_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345GeometryCalibrationRound842Exact as Geometry
import DASHI.Physics.Closure.NSTriadKNR650Rational345EnergyRowsRound829Exact as Energy

F : C3.RealField _
F = Direct.F

------------------------------------------------------------------------
-- Literal resonant incidences.
------------------------------------------------------------------------

τ75₈ τ57₈ τ74₆ τ47₆ τ71₄ τ17₄ τ25₃ τ52₃ : Physical.PhysicalTriadIncidence
τ24₁ τ42₁ τ28₅ τ82₅ τ51₂ τ15₂ τ48₇ τ84₇ : Physical.PhysicalTriadIncidence

τ75₈ = Physical.physicalTriad Active.k₇ Active.k₅ Active.k₈ refl
τ57₈ = Physical.physicalTriad Active.k₅ Active.k₇ Active.k₈ refl
τ74₆ = Physical.physicalTriad Active.k₇ Active.k₄ Active.k₆ refl
τ47₆ = Physical.physicalTriad Active.k₄ Active.k₇ Active.k₆ refl
τ71₄ = Physical.physicalTriad Active.k₇ Active.k₁ Active.k₄ refl
τ17₄ = Physical.physicalTriad Active.k₁ Active.k₇ Active.k₄ refl
τ25₃ = Physical.physicalTriad Active.k₂ Active.k₅ Active.k₃ refl
τ52₃ = Physical.physicalTriad Active.k₅ Active.k₂ Active.k₃ refl
τ24₁ = Physical.physicalTriad Active.k₂ Active.k₄ Active.k₁ refl
τ42₁ = Physical.physicalTriad Active.k₄ Active.k₂ Active.k₁ refl
τ28₅ = Physical.physicalTriad Active.k₂ Active.k₈ Active.k₅ refl
τ82₅ = Physical.physicalTriad Active.k₈ Active.k₂ Active.k₅ refl
τ51₂ = Physical.physicalTriad Active.k₅ Active.k₁ Active.k₂ refl
τ15₂ = Physical.physicalTriad Active.k₁ Active.k₅ Active.k₂ refl
τ48₇ = Physical.physicalTriad Active.k₄ Active.k₈ Active.k₇ refl
τ84₇ = Physical.physicalTriad Active.k₈ Active.k₄ Active.k₇ refl

------------------------------------------------------------------------
-- Expected exact ordered-cell vectors.
------------------------------------------------------------------------

t75₈ t57₈ t74₆ t47₆ t71₄ t17₄ t25₃ t52₃ : C3.Complex3 F
t24₁ t42₁ t28₅ t82₅ t51₂ t15₂ t48₇ t84₇ : C3.Complex3 F

t75₈ = Energy.v ((+ 512) / 25) 0 (- ((+ 384) / 25)) 0 32 0
t57₈ = Energy.v (- ((+ 288) / 25)) 0 ((+ 216) / 25) 0 (- 18) 6
t74₆ = Energy.v 0 ((+ 512) / 25) 0 ((+ 384) / 25) 0 32
t47₆ = Energy.v 0 (- ((+ 288) / 25)) 0 (- ((+ 216) / 25)) 6 18
t71₄ = Energy.v 48 48 0 0 32 0
t17₄ = Energy.v 0 0 0 0 36 18
t25₃ = Energy.v 0 (- ((+ 512) / 25)) 0 (- ((+ 384) / 25)) 0 (- 32)
t52₃ = Energy.v 0 ((+ 288) / 25) 0 ((+ 216) / 25) 6 (- 18)
t24₁ = Energy.v ((+ 512) / 25) 0 (- ((+ 384) / 25)) 0 32 0
t42₁ = Energy.v (- ((+ 288) / 25)) 0 ((+ 216) / 25) 0 (- 18) (- 6)
t28₅ = Energy.v 48 (- 48) 0 0 32 0
t82₅ = Energy.v 0 0 0 0 36 (- 18)
t51₂ = Energy.v 0 0 (- 27) (- 27) 24 0
t15₂ = Energy.v 0 0 0 0 36 36
t48₇ = Energy.v 0 0 (- 27) 27 24 0
t84₇ = Energy.v 0 0 0 0 36 (- 36)

vecRing :
  (left right : C3.Complex3 F) →
  C3.real (C3.x left) ≡ C3.real (C3.x right) →
  C3.imaginary (C3.x left) ≡ C3.imaginary (C3.x right) →
  C3.real (C3.y left) ≡ C3.real (C3.y right) →
  C3.imaginary (C3.y left) ≡ C3.imaginary (C3.y right) →
  C3.real (C3.z left) ≡ C3.real (C3.z right) →
  C3.imaginary (C3.z left) ≡ C3.imaginary (C3.z right) →
  left ≡ right
vecRing left right xr xi yr yi zr zi =
  Algebra.complex3Ext
    (Algebra.complexExt xr xi)
    (Algebra.complexExt yr yi)
    (Algebra.complexExt zr zi)

module Cells
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  module G = Geometry.Geometry unit I

  system : Audit.FiniteComplex3GalerkinSystem F E I
  system = Direct.directAuditSystem E I

  cell75₈ : Audit.projectedOrderedTerm system τ75₈ ≡ t75₈
  cell75₈
    rewrite Snapshot.velocity₇ | Snapshot.velocity₅
          | G.embedPlus3 | G.embedPlus4 | C3.embedZero E | G.inv₈ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell57₈ : Audit.projectedOrderedTerm system τ57₈ ≡ t57₈
  cell57₈
    rewrite Snapshot.velocity₅ | Snapshot.velocity₇
          | G.embedPlus3 | G.embedPlus4 | C3.embedZero E | G.inv₈ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell74₆ : Audit.projectedOrderedTerm system τ74₆ ≡ t74₆
  cell74₆
    rewrite Snapshot.velocity₇ | Snapshot.velocity₄
          | G.embedPlus3 | G.embedMinus4 | C3.embedZero E | G.inv₆ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell47₆ : Audit.projectedOrderedTerm system τ47₆ ≡ t47₆
  cell47₆
    rewrite Snapshot.velocity₄ | Snapshot.velocity₇
          | G.embedPlus3 | G.embedMinus4 | C3.embedZero E | G.inv₆ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell71₄ : Audit.projectedOrderedTerm system τ71₄ ≡ t71₄
  cell71₄
    rewrite Snapshot.velocity₇ | Snapshot.velocity₁
          | G.embedPlus3 | G.embedMinus3 | G.embedMinus4
          | C3.embedZero E | G.inv₄ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell17₄ : Audit.projectedOrderedTerm system τ17₄ ≡ t17₄
  cell17₄
    rewrite Snapshot.velocity₁ | Snapshot.velocity₇
          | G.embedPlus3 | G.embedMinus3 | G.embedMinus4
          | C3.embedZero E | G.inv₄ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell25₃ : Audit.projectedOrderedTerm system τ25₃ ≡ t25₃
  cell25₃
    rewrite Snapshot.velocity₂ | Snapshot.velocity₅
          | G.embedMinus3 | G.embedPlus4 | C3.embedZero E | G.inv₃ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell52₃ : Audit.projectedOrderedTerm system τ52₃ ≡ t52₃
  cell52₃
    rewrite Snapshot.velocity₅ | Snapshot.velocity₂
          | G.embedMinus3 | G.embedPlus4 | C3.embedZero E | G.inv₃ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell24₁ : Audit.projectedOrderedTerm system τ24₁ ≡ t24₁
  cell24₁
    rewrite Snapshot.velocity₂ | Snapshot.velocity₄
          | G.embedMinus3 | G.embedMinus4 | C3.embedZero E | G.inv₁ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell42₁ : Audit.projectedOrderedTerm system τ42₁ ≡ t42₁
  cell42₁
    rewrite Snapshot.velocity₄ | Snapshot.velocity₂
          | G.embedMinus3 | G.embedMinus4 | C3.embedZero E | G.inv₁ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell28₅ : Audit.projectedOrderedTerm system τ28₅ ≡ t28₅
  cell28₅
    rewrite Snapshot.velocity₂ | Snapshot.velocity₈
          | G.embedMinus3 | G.embedPlus3 | G.embedPlus4
          | C3.embedZero E | G.inv₅ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell82₅ : Audit.projectedOrderedTerm system τ82₅ ≡ t82₅
  cell82₅
    rewrite Snapshot.velocity₈ | Snapshot.velocity₂
          | G.embedMinus3 | G.embedPlus3 | G.embedPlus4
          | C3.embedZero E | G.inv₅ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell51₂ : Audit.projectedOrderedTerm system τ51₂ ≡ t51₂
  cell51₂
    rewrite Snapshot.velocity₅ | Snapshot.velocity₁
          | G.embedMinus3 | G.embedMinus4 | G.embedPlus4
          | C3.embedZero E | G.inv₂ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell15₂ : Audit.projectedOrderedTerm system τ15₂ ≡ t15₂
  cell15₂
    rewrite Snapshot.velocity₁ | Snapshot.velocity₅
          | G.embedMinus3 | G.embedMinus4 | G.embedPlus4
          | C3.embedZero E | G.inv₂ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell48₇ : Audit.projectedOrderedTerm system τ48₇ ≡ t48₇
  cell48₇
    rewrite Snapshot.velocity₄ | Snapshot.velocity₈
          | G.embedPlus3 | G.embedPlus4 | G.embedMinus4
          | C3.embedZero E | G.inv₇ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

  cell84₇ : Audit.projectedOrderedTerm system τ84₇ ≡ t84₇
  cell84₇
    rewrite Snapshot.velocity₈ | Snapshot.velocity₄
          | G.embedPlus3 | G.embedPlus4 | G.embedMinus4
          | C3.embedZero E | G.inv₇ =
    vecRing _ _ (solve []) (solve []) (solve []) (solve []) (solve []) (solve [])

round843SixteenOrderedR30CellsSourceWritten : Bool
round843SixteenOrderedR30CellsSourceWritten = true

round843AdditionalNumericalOracleRequired : Bool
round843AdditionalNumericalOracleRequired = false

round843ActiveFibreEnumerationStillRequired : Bool
round843ActiveFibreEnumerationStillRequired = true

round843ClayPromotion : Bool
round843ClayPromotion = false

round843ActiveFibreEnumerationStillRequiredIsTrue :
  round843ActiveFibreEnumerationStillRequired ≡ true
round843ActiveFibreEnumerationStillRequiredIsTrue = refl
