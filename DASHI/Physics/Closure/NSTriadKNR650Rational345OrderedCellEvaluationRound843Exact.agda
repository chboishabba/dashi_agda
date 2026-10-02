{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345OrderedCellEvaluationRound843Exact where

------------------------------------------------------------------------
-- R843E / KERNEL-TARGETED EVALUATION OF THE 16 ACTIVE R30 CELLS
--
-- Uses the direct R841 snapshot and R842 unit-normalized geometry.  After
-- rewriting integer coordinates and output inverse squares, every literal R30
-- ordered interaction is a closed rational Complex3 expression.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345GeometryCalibrationRound842Exact as Geometry
import DASHI.Physics.Closure.NSTriadKNR650Rational345OrderedCellsRound843Exact as Cells

F : C3.RealField _
F = Rational.rationalRealField

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  module G = Geometry.Geometry unit I

  system = Direct.directAuditSystem E I

  cell₁aExact : Audit.projectedOrderedTerm system Cells.t₁a ≡ Cells.c₁a
  cell₁aExact
    rewrite G.embedMinus3 | G.embedMinus4 | C3.embedZero E | G.inv₁ = refl

  cell₁bExact : Audit.projectedOrderedTerm system Cells.t₁b ≡ Cells.c₁b
  cell₁bExact
    rewrite G.embedMinus3 | G.embedMinus4 | C3.embedZero E | G.inv₁ = refl

  cell₂aExact : Audit.projectedOrderedTerm system Cells.t₂a ≡ Cells.c₂a
  cell₂aExact
    rewrite G.embedMinus3 | G.embedPlus4 | C3.embedZero E | G.inv₂ = refl

  cell₂bExact : Audit.projectedOrderedTerm system Cells.t₂b ≡ Cells.c₂b
  cell₂bExact
    rewrite G.embedMinus3 | G.embedMinus4 | C3.embedZero E | G.inv₂ = refl

  cell₃aExact : Audit.projectedOrderedTerm system Cells.t₃a ≡ Cells.c₃a
  cell₃aExact
    rewrite G.embedMinus3 | G.embedPlus4 | C3.embedZero E | G.inv₃ = refl

  cell₃bExact : Audit.projectedOrderedTerm system Cells.t₃b ≡ Cells.c₃b
  cell₃bExact
    rewrite G.embedMinus3 | G.embedPlus4 | C3.embedZero E | G.inv₃ = refl

  cell₄aExact : Audit.projectedOrderedTerm system Cells.t₄a ≡ Cells.c₄a
  cell₄aExact
    rewrite G.embedPlus3 | G.embedMinus4 | C3.embedZero E | G.inv₄ = refl

  cell₄bExact : Audit.projectedOrderedTerm system Cells.t₄b ≡ Cells.c₄b
  cell₄bExact
    rewrite G.embedMinus3 | G.embedMinus4 | C3.embedZero E | G.inv₄ = refl

  cell₅aExact : Audit.projectedOrderedTerm system Cells.t₅a ≡ Cells.c₅a
  cell₅aExact
    rewrite G.embedPlus3 | G.embedPlus4 | C3.embedZero E | G.inv₅ = refl

  cell₅bExact : Audit.projectedOrderedTerm system Cells.t₅b ≡ Cells.c₅b
  cell₅bExact
    rewrite G.embedMinus3 | G.embedPlus4 | C3.embedZero E | G.inv₅ = refl

  cell₆aExact : Audit.projectedOrderedTerm system Cells.t₆a ≡ Cells.c₆a
  cell₆aExact
    rewrite G.embedPlus3 | G.embedMinus4 | C3.embedZero E | G.inv₆ = refl

  cell₆bExact : Audit.projectedOrderedTerm system Cells.t₆b ≡ Cells.c₆b
  cell₆bExact
    rewrite G.embedPlus3 | G.embedMinus4 | C3.embedZero E | G.inv₆ = refl

  cell₇aExact : Audit.projectedOrderedTerm system Cells.t₇a ≡ Cells.c₇a
  cell₇aExact
    rewrite G.embedPlus3 | G.embedPlus4 | C3.embedZero E | G.inv₇ = refl

  cell₇bExact : Audit.projectedOrderedTerm system Cells.t₇b ≡ Cells.c₇b
  cell₇bExact
    rewrite G.embedPlus3 | G.embedMinus4 | C3.embedZero E | G.inv₇ = refl

  cell₈aExact : Audit.projectedOrderedTerm system Cells.t₈a ≡ Cells.c₈a
  cell₈aExact
    rewrite G.embedPlus3 | G.embedPlus4 | C3.embedZero E | G.inv₈ = refl

  cell₈bExact : Audit.projectedOrderedTerm system Cells.t₈b ≡ Cells.c₈b
  cell₈bExact
    rewrite G.embedPlus3 | G.embedPlus4 | C3.embedZero E | G.inv₈ = refl

  evaluation : Cells.Evaluate.OrderedCellEvaluation E I (Geometry.unit-345-geometry unit)
  evaluation = record
    { Cells.Evaluate.cell₁a = cell₁aExact
    ; Cells.Evaluate.cell₁b = cell₁bExact
    ; Cells.Evaluate.cell₂a = cell₂aExact
    ; Cells.Evaluate.cell₂b = cell₂bExact
    ; Cells.Evaluate.cell₃a = cell₃aExact
    ; Cells.Evaluate.cell₃b = cell₃bExact
    ; Cells.Evaluate.cell₄a = cell₄aExact
    ; Cells.Evaluate.cell₄b = cell₄bExact
    ; Cells.Evaluate.cell₅a = cell₅aExact
    ; Cells.Evaluate.cell₅b = cell₅bExact
    ; Cells.Evaluate.cell₆a = cell₆aExact
    ; Cells.Evaluate.cell₆b = cell₆bExact
    ; Cells.Evaluate.cell₇a = cell₇aExact
    ; Cells.Evaluate.cell₇b = cell₇bExact
    ; Cells.Evaluate.cell₈a = cell₈aExact
    ; Cells.Evaluate.cell₈b = cell₈bExact
    }

round843ESixteenLiteralR30CellsKernelTargeted : Bool
round843ESixteenLiteralR30CellsKernelTargeted = true

round843EAdditionalNumericalOracleRequired : Bool
round843EAdditionalNumericalOracleRequired = false

round843EClayPromotion : Bool
round843EClayPromotion = false
