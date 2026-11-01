module DASHI.Physics.YangMills.BalabanCMP109EliminatedCoordinateDerivativeExact where

------------------------------------------------------------------------
-- ROW A1: DERIVATIVE OF THE ELIMINATED-COORDINATE EMBEDDING C(U)
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- SOURCE FACT
--
-- After CMP99 (3.156) the constrained fluctuation space is parametrized by free
-- bond variables B.  The embedding C(U) is the identity on almost all bonds; on
-- each selected eliminated bond b0(c), (C(U)B)(b0) is the solution of
--
--     (Q(U) C(U) B)(c) = 0.
--
-- CMP109 Sect. 2 uses the same mechanism after linearizing the nonlinear
-- fluctuation average.  Differentiating the fixed constraint identity gives
--
--     Q C' = - Q' C.
--
-- This file proves only the exact finite rational rearrangement once the literal
-- differentiated product rule is supplied.  Recovering Q'(U) and the selected
-- pivot solve from CMP98/CMP99 remains the physical source calculation.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record EliminatedCoordinateDerivativeData (Free Multiplier : Set) : Set₁ where
  field
    qPrimeAfterC qAfterCPrime : Free → Multiplier → ℚ

    -- Derivative of Q(U) C(U) = 0 on every free vector / constraint row:
    --     Q' C + Q C' = 0.
    differentiatedConstraint : ∀ free row →
      qPrimeAfterC free row + qAfterCPrime free row ≡ 0ℚ

open EliminatedCoordinateDerivativeData public

eliminatedCoordinateDerivativeEquation :
  ∀ {Free Multiplier}
    (dataSet : EliminatedCoordinateDerivativeData Free Multiplier)
    free row →
  qAfterCPrime dataSet free row ≡ - qPrimeAfterC dataSet free row
eliminatedCoordinateDerivativeEquation dataSet free row =
  let
    source = differentiatedConstraint dataSet free row
    rearrange : ∀ left right → left + right ≡ 0ℚ → right ≡ - left
    rearrange left right equality =
      trans
        (ℚRing.solve-∀ left right)
        (trans
          (cong (λ selected → selected - left) equality)
          (ℚRing.solve-∀ left))
  in
  rearrange
    (qPrimeAfterC dataSet free row)
    (qAfterCPrime dataSet free row)
    source
  where
    open import Relation.Binary.PropositionalEquality using (cong)

eliminatedCoordinateDerivativeAlgebraLevel : ProofLevel
eliminatedCoordinateDerivativeAlgebraLevel = machineChecked

-- Physical/source seams.
cmp99LiteralQPrimeLevel : ProofLevel
cmp99LiteralQPrimeLevel = conditional

cmp99LiteralEliminatedPivotDerivativeLevel : ProofLevel
cmp99LiteralEliminatedPivotDerivativeLevel = conditional

cmp109LiteralCPrimeFromConstraintLevel : ProofLevel
cmp109LiteralCPrimeFromConstraintLevel = conditional
