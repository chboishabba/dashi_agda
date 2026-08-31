module DASHI.Physics.YangMills.BalabanCMP99EliminatedPivotDerivativeExact where

------------------------------------------------------------------------
-- ROW A1: EXACT DERIVATIVE OF THE CMP99 ELIMINATED PIVOT COORDINATE
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- SOURCE FACT
--
-- After CMP99 (3.156), C(U) is the identity on all free bonds and differs only
-- on the selected eliminated bond b0(c) in each constraint row.  That selected
-- coordinate is the solution of
--
--       (Q(U) C(U) B)(c) = 0.
--
-- Hence C'(U) is zero on the unchanged free coordinates.  On b0(c), after
-- differentiating Q C = 0, one obtains the one-pivot equation
--
--       a_c C'_c(B) + (Q' C B)(c) = 0,
--
-- where a_c is the coefficient of the selected eliminated coordinate in the
-- current linear constraint row.  If a_c is nonzero, the exact solution is
--
--       C'_c(B) = - a_c^{-1} (Q' C B)(c).
--
-- This module closes that finite rational solve.  The remaining source task is
-- to identify/bound the literal pivot coefficient and compute Q' from CMP98/99.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; 1/_; NonZero)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record EliminatedPivotDerivativeData : Set where
  field
    pivotCoefficient : ℚ
    pivotNonzero : NonZero pivotCoefficient
    qPrimeAfterC : ℚ
    eliminatedCoordinatePrime : ℚ

    differentiatedPivotEquation :
      pivotCoefficient * eliminatedCoordinatePrime + qPrimeAfterC ≡ 0ℚ

open EliminatedPivotDerivativeData public

pivotInverse : EliminatedPivotDerivativeData → ℚ
pivotInverse dataSet =
  let instance nonzero = pivotNonzero dataSet
  in 1/ pivotCoefficient dataSet

pivotInverseRight : ∀ dataSet →
  pivotCoefficient dataSet * pivotInverse dataSet ≡ 1ℚ
pivotInverseRight dataSet =
  let instance nonzero = pivotNonzero dataSet
  in ℚP.*-inverseʳ (pivotCoefficient dataSet)

eliminatedPivotDerivativeExact : ∀ dataSet →
  eliminatedCoordinatePrime dataSet
  ≡ - (pivotInverse dataSet * qPrimeAfterC dataSet)
eliminatedPivotDerivativeExact dataSet =
  let
    a = pivotCoefficient dataSet
    aInv = pivotInverse dataSet
    cPrime = eliminatedCoordinatePrime dataSet
    source = qPrimeAfterC dataSet

    scaled :
      aInv * (a * cPrime + source) ≡ aInv * 0ℚ
    scaled = cong (aInv *_) (differentiatedPivotEquation dataSet)

    simplify :
      aInv * (a * cPrime + source)
      ≡ cPrime + aInv * source
    simplify =
      trans
        (ℚRing.solve-∀ aInv a cPrime source)
        (cong (λ selected → selected * cPrime + aInv * source)
          (trans
            (ℚP.*-comm aInv a)
            (pivotInverseRight dataSet)))

    zeroRight : aInv * 0ℚ ≡ 0ℚ
    zeroRight = ℚP.*-zeroʳ aInv

    sumZero : cPrime + aInv * source ≡ 0ℚ
    sumZero = trans (sym simplify) (trans scaled zeroRight)
  in
  trans
    (ℚRing.solve-∀ cPrime aInv source)
    (trans
      (cong (λ selected → selected - aInv * source) sumZero)
      (ℚRing.solve-∀ aInv source))

------------------------------------------------------------------------
-- Support statement: unchanged free coordinates have zero derivative.
------------------------------------------------------------------------

record EliminatedCoordinateSupport (Coordinate : Set) : Set₁ where
  field
    isEliminated : Coordinate → Set
    coordinatePrime : Coordinate → ℚ
    freeCoordinatePrimeZero : ∀ coordinate →
      (isEliminated coordinate → 0ℚ ≡ 1ℚ) →
      coordinatePrime coordinate ≡ 0ℚ

open EliminatedCoordinateSupport public

cmp99EliminatedPivotDerivativeAlgebraLevel : ProofLevel
cmp99EliminatedPivotDerivativeAlgebraLevel = machineChecked

-- Source-facing leaves: identify the selected pivot coefficient of literal
-- Q(U), prove its nonvanishing on the source small-field region, and instantiate
-- qPrimeAfterC from the differentiated one-step averaging operator.
cmp99LiteralEliminatedPivotCoefficientLevel : ProofLevel
cmp99LiteralEliminatedPivotCoefficientLevel = conditional

cmp99LiteralEliminatedPivotDerivativeLevel : ProofLevel
cmp99LiteralEliminatedPivotDerivativeLevel = conditional
