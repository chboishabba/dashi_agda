{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109EliminatedCoordinateDerivativeRound125Exact where

------------------------------------------------------------------------
-- ROUND125 A1: DIFFERENTIATED ELIMINATED-COORDINATE CONSTRAINT
--
-- Primary sources:
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", CMP 99 (1985), 389--434. DOI 10.1007/BF01240355.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", CMP 109 (1987), 249--301. DOI 10.1007/BF01215223.
--
-- On the free-coordinate parametrisation C(U), the constraint is Q(U)C(U)=0.
-- Differentiation gives Q'C + QC'=0.  The exact rearrangement below proves
--
--                         QC' = - Q'C.
--
-- Round124 then solves the selected CMP99 pivot explicitly once Q'C and the
-- nonzero pivot coefficient are instantiated.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record EliminatedCoordinateDerivativeData (Free ConstraintRow : Set) : Set₁ where
  field
    qPrimeAfterC qAfterCPrime : Free → ConstraintRow → ℚ
    differentiatedConstraint : ∀ free row →
      qPrimeAfterC free row + qAfterCPrime free row ≡ 0ℚ

open EliminatedCoordinateDerivativeData public

eliminatedCoordinateDerivativeEquation :
  ∀ {Free ConstraintRow}
    (dataSet : EliminatedCoordinateDerivativeData Free ConstraintRow)
    free row →
  qAfterCPrime dataSet free row ≡ - qPrimeAfterC dataSet free row
eliminatedCoordinateDerivativeEquation dataSet free row =
  let
    left = qPrimeAfterC dataSet free row
    right = qAfterCPrime dataSet free row
    source = differentiatedConstraint dataSet free row
  in
  trans
    (ℚRing.solve-∀ left right)
    (trans
      (cong (λ selected → selected - left) source)
      (ℚRing.solve-∀ left))

cmp109EliminatedCoordinateDerivativeAlgebraRound125Level : ProofLevel
cmp109EliminatedCoordinateDerivativeAlgebraRound125Level = machineChecked

-- No abstract C' estimate remains at this algebraic layer.  The source-facing
-- task is Q'(U) from the literal CMP98 averaging formula plus the pivot data of
-- Round124.
literalCMP98QPrimeToCMP109CPrimeRound125Level : ProofLevel
literalCMP98QPrimeToCMP109CPrimeRound125Level = conditional
