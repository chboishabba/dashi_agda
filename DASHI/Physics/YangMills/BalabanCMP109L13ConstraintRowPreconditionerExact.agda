module DASHI.Physics.YangMills.BalabanCMP109L13ConstraintRowPreconditionerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Remove the artificial 13^-4 conditioning of the normalized L=13 block
-- average by the exact rational row rescaling 13^2=169.  Since 13^4=28561,
-- the already-proved normalized adjoint identity
--
--       ||Q* lambda||^2 = (1/28561) ||lambda||^2
--
-- becomes
--
--       ||(169 Q)* lambda||^2 = ||lambda||^2.
--
-- No square root or irrational scalar is introduced.  This is a coordinate
-- preconditioner on the constraint codomain; the generic zero-fibre/kernel/
-- tangent-projector invariance is proved in
-- BalabanConstraintRowPreconditioningExact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong; sumRationalScale)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal
import DASHI.Physics.YangMills.BalabanCMP109L13BlockAverageAdjointFloorExact as Average
import DASHI.Physics.YangMills.BalabanConstraintRowPreconditioningExact as RowChange

oneHundredSixtyNine : ℚ
oneHundredSixtyNine = + 169 / 1

oneOverOneHundredSixtyNine : ℚ
oneOverOneHundredSixtyNine = + 1 / 169

scaleState : ℚ → Average.StateVector → Average.StateVector
scaleState coefficient vector state = coefficient * vector state

stateNormScaleExact : ∀ coefficient vector →
  Average.stateNormSq (scaleState coefficient vector)
  ≡ coefficient * coefficient * Average.stateNormSq vector
stateNormScaleExact coefficient vector =
  trans
    (sumRationalCong
      (Physical.physicalSU2Coordinates Side13.side13)
      (λ state → sq (scaleState coefficient vector state))
      (λ state → coefficient * coefficient * sq (vector state))
      (λ state → ℚRing.solve-∀ coefficient (vector state)))
    (trans
      (sumRationalScale
        (coefficient * coefficient)
        (Physical.physicalSU2Coordinates Side13.side13)
        (λ state → sq (vector state)))
      refl)

preconditionedBlockAverageAdjoint : Average.RowVector → Average.StateVector
preconditionedBlockAverageAdjoint multiplier =
  scaleState oneHundredSixtyNine
    (Average.normalizedBlockAverageAdjoint multiplier)

preconditionedAverageAdjointNormExact : ∀ multiplier →
  Average.stateNormSq (preconditionedBlockAverageAdjoint multiplier)
  ≡ Average.rowNormSq multiplier
preconditionedAverageAdjointNormExact multiplier =
  trans
    (stateNormScaleExact oneHundredSixtyNine
      (Average.normalizedBlockAverageAdjoint multiplier))
    (trans
      (cong
        (λ value → oneHundredSixtyNine * oneHundredSixtyNine * value)
        (Average.normalizedAdjointNormExact multiplier))
      (ℚRing.solve-∀ (Average.rowNormSq multiplier)))

preconditionedAverageAdjointFloor : ∀ multiplier →
  Average.rowNormSq multiplier
  ≡ Average.stateNormSq (preconditionedBlockAverageAdjoint multiplier)
preconditionedAverageAdjointFloor multiplier =
  symExact (preconditionedAverageAdjointNormExact multiplier)
  where
  symExact : ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
  symExact refl = refl

------------------------------------------------------------------------
-- Scalar row map and its exact inverse.  These are the coefficients used on
-- each of the twelve block-average rows; gauge rows are left unchanged by the
-- combined source-scale preconditioner.
------------------------------------------------------------------------

scaleAverageRow : ℚ → ℚ
scaleAverageRow value = oneHundredSixtyNine * value

unscaleAverageRow : ℚ → ℚ
unscaleAverageRow value = oneOverOneHundredSixtyNine * value

unscaleScaleAverageRow : ∀ value →
  unscaleAverageRow (scaleAverageRow value) ≡ value
unscaleScaleAverageRow value = ℚRing.solve-∀ value

scaleUnscaleAverageRow : ∀ value →
  scaleAverageRow (unscaleAverageRow value) ≡ value
scaleUnscaleAverageRow value = ℚRing.solve-∀ value

averageScalarRowChange : RowChange.InvertibleRowChange ℚ
averageScalarRowChange = record
  { RowChange.InvertibleRowChange.forward = scaleAverageRow
  ; RowChange.InvertibleRowChange.backward = unscaleAverageRow
  ; RowChange.InvertibleRowChange.backwardForward = unscaleScaleAverageRow
  ; RowChange.InvertibleRowChange.forwardBackward = scaleUnscaleAverageRow
  }

l13ConstraintAverageRowPreconditioningLevel : ProofLevel
l13ConstraintAverageRowPreconditioningLevel = machineChecked

l13PreconditionedAverageAdjointIsometryLevel : ProofLevel
l13PreconditionedAverageAdjointIsometryLevel = machineChecked
