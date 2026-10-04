{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345OrderedCellsRound843Exact where

------------------------------------------------------------------------
-- R843 / EXACT 16 ORDERED R30 CELLS OF THE 3-4-5 SNAPSHOT
--
-- R840 reduces the literal projected nonlinearity to seed-pair incidences.
-- There are exactly two nonzero ordered seed pairs at each of the eight active
-- outputs.  This owner evaluates those literal Audit.projectedOrderedTerm
-- expressions in the direct R841 physical system, under only the ordinary
-- unit-preserving Fourier normalization from R842.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345EnergyRowsRound829Exact as Energy
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345UnitGeometryRound842Exact as Geometry

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Explicit resonant incidences.  The resonance fields are definitional.
------------------------------------------------------------------------

t₁a t₁b t₂a t₂b t₃a t₃b t₄a t₄b
  t₅a t₅b t₆a t₆b t₇a t₇b t₈a t₈b :
  Physical.PhysicalTriadIncidence

t₁a = Physical.physicalTriad Active.k₂ Active.k₄ Active.k₁ refl
t₁b = Physical.physicalTriad Active.k₄ Active.k₂ Active.k₁ refl

t₂a = Physical.physicalTriad Active.k₁ Active.k₅ Active.k₂ refl
t₂b = Physical.physicalTriad Active.k₅ Active.k₁ Active.k₂ refl

t₃a = Physical.physicalTriad Active.k₂ Active.k₅ Active.k₃ refl
t₃b = Physical.physicalTriad Active.k₅ Active.k₂ Active.k₃ refl

t₄a = Physical.physicalTriad Active.k₁ Active.k₇ Active.k₄ refl
t₄b = Physical.physicalTriad Active.k₇ Active.k₁ Active.k₄ refl

t₅a = Physical.physicalTriad Active.k₂ Active.k₈ Active.k₅ refl
t₅b = Physical.physicalTriad Active.k₈ Active.k₂ Active.k₅ refl

t₆a = Physical.physicalTriad Active.k₄ Active.k₇ Active.k₆ refl
t₆b = Physical.physicalTriad Active.k₇ Active.k₄ Active.k₆ refl

t₇a = Physical.physicalTriad Active.k₄ Active.k₈ Active.k₇ refl
t₇b = Physical.physicalTriad Active.k₈ Active.k₄ Active.k₇ refl

t₈a = Physical.physicalTriad Active.k₅ Active.k₇ Active.k₈ refl
t₈b = Physical.physicalTriad Active.k₇ Active.k₅ Active.k₈ refl

------------------------------------------------------------------------
-- Exact ordered-cell targets from the independent R829 certificate.
------------------------------------------------------------------------

c₁a c₁b c₂a c₂b c₃a c₃b c₄a c₄b
  c₅a c₅b c₆a c₆b c₇a c₇b c₈a c₈b :
  C3.Complex3 F

c₁a = Energy.v ((+ 512) / 25) 0 (- ((+ 384) / 25)) 0 32 0
c₁b = Energy.v (- ((+ 288) / 25)) 0 ((+ 216) / 25) 0 (- 18) (- 6)

c₂a = Energy.v 0 0 0 0 36 36
c₂b = Energy.v 0 0 (- 27) (- 27) 24 0

c₃a = Energy.v 0 (- ((+ 512) / 25)) 0 (- ((+ 384) / 25)) 0 (- 32)
c₃b = Energy.v 0 ((+ 288) / 25) 0 ((+ 216) / 25) 6 (- 18)

c₄a = Energy.v 0 0 0 0 36 18
c₄b = Energy.v 48 48 0 0 32 0

c₅a = Energy.v 48 (- 48) 0 0 32 0
c₅b = Energy.v 0 0 0 0 36 (- 18)

c₆a = Energy.v 0 (- ((+ 288) / 25)) 0 (- ((+ 216) / 25)) 6 18
c₆b = Energy.v 0 ((+ 512) / 25) 0 ((+ 384) / 25) 0 32

c₇a = Energy.v 0 0 (- 27) 27 24 0
c₇b = Energy.v 0 0 0 0 36 (- 36)

c₈a = Energy.v (- ((+ 288) / 25)) 0 ((+ 216) / 25) 0 (- 18) 6
c₈b = Energy.v ((+ 512) / 25) 0 (- ((+ 384) / 25)) 0 32 0

------------------------------------------------------------------------
-- One finite evaluator interface.  These are intentionally stated directly
-- against Audit.projectedOrderedTerm rather than a duplicated formula.
------------------------------------------------------------------------

module Evaluate
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (G : Geometry.Unit345Geometry E I) where

  system = Direct.directAuditSystem E I

  record OrderedCellEvaluation : Set where
    field
      cell₁a : Audit.projectedOrderedTerm system t₁a ≡ c₁a
      cell₁b : Audit.projectedOrderedTerm system t₁b ≡ c₁b
      cell₂a : Audit.projectedOrderedTerm system t₂a ≡ c₂a
      cell₂b : Audit.projectedOrderedTerm system t₂b ≡ c₂b
      cell₃a : Audit.projectedOrderedTerm system t₃a ≡ c₃a
      cell₃b : Audit.projectedOrderedTerm system t₃b ≡ c₃b
      cell₄a : Audit.projectedOrderedTerm system t₄a ≡ c₄a
      cell₄b : Audit.projectedOrderedTerm system t₄b ≡ c₄b
      cell₅a : Audit.projectedOrderedTerm system t₅a ≡ c₅a
      cell₅b : Audit.projectedOrderedTerm system t₅b ≡ c₅b
      cell₆a : Audit.projectedOrderedTerm system t₆a ≡ c₆a
      cell₆b : Audit.projectedOrderedTerm system t₆b ≡ c₆b
      cell₇a : Audit.projectedOrderedTerm system t₇a ≡ c₇a
      cell₇b : Audit.projectedOrderedTerm system t₇b ≡ c₇b
      cell₈a : Audit.projectedOrderedTerm system t₈a ≡ c₈a
      cell₈b : Audit.projectedOrderedTerm system t₈b ≡ c₈b

  open OrderedCellEvaluation public

round843SixteenLiteralR30CellTargetsExposed : Bool
round843SixteenLiteralR30CellTargetsExposed = true

round843SixteenLiteralR30CellsEvaluatedInKernel : Bool
round843SixteenLiteralR30CellsEvaluatedInKernel = false

round843AdditionalAnalyticEstimateRequired : Bool
round843AdditionalAnalyticEstimateRequired = false

round843ClayPromotion : Bool
round843ClayPromotion = false
