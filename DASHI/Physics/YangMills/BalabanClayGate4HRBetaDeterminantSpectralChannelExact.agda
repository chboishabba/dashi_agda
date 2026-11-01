module DASHI.Physics.YangMills.BalabanClayGate4HRBetaDeterminantSpectralChannelExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HR

------------------------------------------------------------------------
-- Local determinant channel from spectral logarithm remainders.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
--
-- On a positive finite carrier, write the relative perturbation spectrum as
-- lambda_j.  The nonlinear determinant contribution is the finite sum
--
--   sum_j (log(1 + lambda_j) - lambda_j).
--
-- This module proves that modewise absolute Taylor bounds imply the local
-- determinant-channel estimate by finite absolute-triangle and pointwise
-- monotonicity.  The remaining physical work is the localized spectral
-- identification and the scalar small-ball logarithm estimate for each mode.
------------------------------------------------------------------------

record LocalDeterminantSpectralData
    (Cell Mode Scalar : Set) : Set₁ where
  field
    algebra : HR.OrderedAbsoluteAdditiveAlgebra Scalar

    modes : Cell → List Mode
    spectralShift : Cell → Mode → Scalar

    logarithmOnePlus : Scalar → Scalar
    subtract : Scalar → Scalar → Scalar

    modeRemainder : Cell → Mode → Scalar
    modeRemainderMeaning : ∀ cell mode →
      modeRemainder cell mode
      ≡ subtract
          (logarithmOnePlus (spectralShift cell mode))
          (spectralShift cell mode)

    modeBudget : Cell → Mode → Scalar

    modeRemainderEstimate : ∀ cell mode →
      HR.LessEqual algebra
        (HR.absolute algebra (modeRemainder cell mode))
        (modeBudget cell mode)

    determinantRemainder : Cell → Scalar
    determinantRemainderMeaning : ∀ cell →
      determinantRemainder cell
      ≡ HR.finiteSum algebra
          (HR.mapList (modeRemainder cell) (modes cell))

    determinantBudget : Cell → Scalar
    determinantBudgetMeaning : ∀ cell →
      determinantBudget cell
      ≡ HR.finiteSum algebra
          (HR.mapList (modeBudget cell) (modes cell))

open LocalDeterminantSpectralData public

localDeterminantRemainderEstimate :
  ∀ {Cell Mode Scalar}
    (dataSet : LocalDeterminantSpectralData Cell Mode Scalar)
    cell →
  HR.LessEqual (algebra dataSet)
    (HR.absolute (algebra dataSet)
      (determinantRemainder dataSet cell))
    (determinantBudget dataSet cell)
localDeterminantRemainderEstimate dataSet cell =
  subst
    (λ upper →
      HR.LessEqual (algebra dataSet)
        (HR.absolute (algebra dataSet)
          (determinantRemainder dataSet cell)) upper)
    (sym (determinantBudgetMeaning dataSet cell))
    (subst
      (λ selectedRemainder →
        HR.LessEqual (algebra dataSet)
          (HR.absolute (algebra dataSet) selectedRemainder)
          (HR.finiteSum (algebra dataSet)
            (HR.mapList (modeBudget dataSet cell)
              (modes dataSet cell))))
      (determinantRemainderMeaning dataSet cell)
      (HR.transitive (algebra dataSet)
        (HR.absoluteFiniteSumBelowSumAbsolute
          (algebra dataSet)
          (HR.mapList (modeRemainder dataSet cell)
            (modes dataSet cell)))
        (HR.finiteSumPointwiseMonotone
          (algebra dataSet)
          (λ mode →
            HR.absolute (algebra dataSet)
              (modeRemainder dataSet cell mode))
          (modeBudget dataSet cell)
          (modes dataSet cell)
          (modeRemainderEstimate dataSet cell))))

record UniformScalarLogRemainder
    (Scalar : Set) : Set₁ where
  field
    absolute : Scalar → Scalar
    logarithmOnePlus : Scalar → Scalar
    subtract multiply divide : Scalar → Scalar → Scalar
    one two theta : Scalar
    StrictlyBelow : Scalar → Scalar → Set
    LessEqual : Scalar → Scalar → Set

    thetaBelowOne : StrictlyBelow theta one

    admissibleShift : Scalar → Set

    scalarTaylorRemainder : ∀ shift →
      admissibleShift shift →
      LessEqual
        (absolute
          (subtract (logarithmOnePlus shift) shift))
        (divide
          (multiply theta theta)
          (multiply two (subtract one theta)))

open UniformScalarLogRemainder public

localDeterminantSpectralTriangleLevel : ProofLevel
localDeterminantSpectralTriangleLevel = machineChecked

scalarLogOnePlusQuadraticRemainderLevel : ProofLevel
scalarLogOnePlusQuadraticRemainderLevel = standardImported

physicalLocalRelativeSpectrumInputsLevel : ProofLevel
physicalLocalRelativeSpectrumInputsLevel = conditional

physicalLocalScalarLogRemainderInputsLevel : ProofLevel
physicalLocalScalarLogRemainderInputsLevel = conditional
