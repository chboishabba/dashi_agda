module DASHI.Physics.YangMills.BalabanClayT3UniformFluctuationSchurExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRelativeHessianCoercivity as Relative
import DASHI.Physics.YangMills.BalabanClayT3OperatorSchurComplementExact as Schur
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3

------------------------------------------------------------------------
-- Literature normalization.
--
-- E. V. Haynsworth,
-- "Determination of the inertia of a partitioned Hermitian matrix",
-- Linear Algebra and its Applications 1 (1968), 73--81.
-- DOI: 10.1016/0024-3795(68)90050-5
--
-- The algebraic Schur identity is inexpensive.  The physical theorem is the
-- scale-, volume- and patch-uniform lower bound on the fluctuation block.  This
-- module connects that theorem to the repository's existing relative-Hessian
-- stability mechanism instead of hiding it inside the proposition name
-- `FluctuationCoercive`.
------------------------------------------------------------------------

record UniformFluctuationSchurFamily
    (Index Coarse Fluctuation Bound : Set) : Set₁ where
  field
    relativeCoercivity :
      Relative.RelativeHessianCoercivityData Index Fluctuation Bound

    schurDataAt : Index → Schur.OperatorSchurData Coarse Fluctuation Bound

    fluctuationHessianMatches : ∀ index →
      Schur.fluctuationHessian (schurDataAt index)
      ≡ Relative.fullHessian relativeCoercivity index

    fluctuationGreenMatches : ∀ index →
      Schur.fluctuationGreen (schurDataAt index)
      ≡ Relative.green relativeCoercivity index

open UniformFluctuationSchurFamily public

uniformFluctuationBlockCoercive :
  ∀ {Index Coarse Fluctuation Bound}
    (dataSet : UniformFluctuationSchurFamily
      Index Coarse Fluctuation Bound)
    index fluctuation →
  Relative.GaugeFixedTangent (relativeCoercivity dataSet) index fluctuation →
  Relative.LessEqual (relativeCoercivity dataSet)
    (Relative.scale (relativeCoercivity dataSet)
      (Relative.cH (relativeCoercivity dataSet))
      (Relative.normSq (relativeCoercivity dataSet) fluctuation))
    (Relative.inner (relativeCoercivity dataSet) fluctuation
      (Schur.fluctuationHessian (schurDataAt dataSet index) fluctuation))
uniformFluctuationBlockCoercive dataSet index fluctuation tangent =
  subst
    (λ selectedHessian →
      Relative.LessEqual (relativeCoercivity dataSet)
        (Relative.scale (relativeCoercivity dataSet)
          (Relative.cH (relativeCoercivity dataSet))
          (Relative.normSq (relativeCoercivity dataSet) fluctuation))
        (Relative.inner (relativeCoercivity dataSet) fluctuation
          (selectedHessian fluctuation)))
    (sym (fluctuationHessianMatches dataSet index))
    (Relative.relativePerturbationPreservesCoercivity
      (relativeCoercivity dataSet) index fluctuation tangent)

uniformFluctuationCoefficientPositive :
  ∀ {Index Coarse Fluctuation Bound}
    (dataSet : UniformFluctuationSchurFamily
      Index Coarse Fluctuation Bound) →
  Relative.Positive (relativeCoercivity dataSet)
    (Relative.cH (relativeCoercivity dataSet))
uniformFluctuationCoefficientPositive dataSet =
  Relative.cHPositive (relativeCoercivity dataSet)

exactSchurComplementAt :
  ∀ {Index Coarse Fluctuation Bound}
    (dataSet : UniformFluctuationSchurFamily
      Index Coarse Fluctuation Bound)
    index →
  P3.ExactSchurComplement Coarse Fluctuation Bound
exactSchurComplementAt dataSet index =
  Schur.operatorExactSchurComplement (schurDataAt dataSet index)

uniformFluctuationCoercivityReductionLevel : ProofLevel
uniformFluctuationCoercivityReductionLevel = machineChecked

uniformFluctuationPositiveConstantLevel : ProofLevel
uniformFluctuationPositiveConstantLevel = machineChecked

uniformOperatorSchurFamilyLevel : ProofLevel
uniformOperatorSchurFamilyLevel = machineChecked

-- Literal completion still requires one reference coercivity constant and one
-- relative perturbation estimate that are independent of lattice spacing,
-- volume and patch regime, together with exact gauge-kernel removal.
physicalUniformFluctuationInputsLevel : ProofLevel
physicalUniformFluctuationInputsLevel = conditional
