module DASHI.Physics.YangMills.BalabanClayGate4SU2HaarJacobianDefectExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Algebraic Haar-density defect from the normalized sine coefficient.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- In the selected SU(2) exponential coordinates the radial Haar density is a
-- square of a normalized sine coefficient (up to the fixed normalization
-- convention).  The exact factorization 1-s^2=(1-s)(1+s) turns the Bishop sine
-- remainder into a chart-density estimate before the scalar log estimate.
------------------------------------------------------------------------

record HaarJacobianDefectAlgebra (Scalar : Set) : Set₁ where
  field
    zero one two : Scalar
    add subtract multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotoneNonnegative : ∀ {left leftUpper right rightUpper} →
      LessEqual zero left → LessEqual left leftUpper →
      LessEqual zero right → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

open HaarJacobianDefectAlgebra public

record SU2HaarJacobianDefect
    {Scalar : Set} (algebra : HaarJacobianDefectAlgebra Scalar) : Set₁ where
  field
    normalizedSine density densityDefect sineDefect sineDefectBudget : Scalar

    densityMeaning :
      density ≡ multiply algebra normalizedSine normalizedSine

    densityDefectMeaning :
      densityDefect ≡ subtract algebra (one algebra) density

    sineDefectMeaning :
      sineDefect ≡ subtract algebra (one algebra) normalizedSine

    defectFactorization :
      densityDefect
      ≡ multiply algebra sineDefect
          (add algebra (one algebra) normalizedSine)

    zeroBelowSineDefect :
      LessEqual algebra (zero algebra) sineDefect
    sineDefectBelowBudget :
      LessEqual algebra sineDefect sineDefectBudget

    zeroBelowOnePlusSine :
      LessEqual algebra (zero algebra)
        (add algebra (one algebra) normalizedSine)
    onePlusSineBelowTwo :
      LessEqual algebra
        (add algebra (one algebra) normalizedSine)
        (two algebra)

open SU2HaarJacobianDefect public

haarDensityDefectBelowTwiceSineBudget :
  ∀ {Scalar}
    {algebra : HaarJacobianDefectAlgebra Scalar} →
  (dataSet : SU2HaarJacobianDefect algebra) →
  LessEqual algebra
    (densityDefect dataSet)
    (multiply algebra (sineDefectBudget dataSet) (two algebra))
haarDensityDefectBelowTwiceSineBudget {algebra = algebra} dataSet =
  subst
    (λ lower → LessEqual algebra lower
      (multiply algebra (sineDefectBudget dataSet) (two algebra)))
    (sym (defectFactorization dataSet))
    (multiplyMonotoneNonnegative algebra
      (zeroBelowSineDefect dataSet)
      (sineDefectBelowBudget dataSet)
      (zeroBelowOnePlusSine dataSet)
      (onePlusSineBelowTwo dataSet))

su2HaarDensityFactorizationLevel : ProofLevel
su2HaarDensityFactorizationLevel = machineChecked

su2HaarDensityDefectBoundLevel : ProofLevel
su2HaarDensityDefectBoundLevel = machineChecked

physicalSU2HaarDensityIdentificationInputsLevel : ProofLevel
physicalSU2HaarDensityIdentificationInputsLevel = conditional

physicalSU2HaarLogRemainderInputsLevel : ProofLevel
physicalSU2HaarLogRemainderInputsLevel = conditional
