module DASHI.Physics.YangMills.BalabanClayGate4PrimaryBetaFiniteDifferenceExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The primary coupling relation is represented in finite-difference form:
--
--   inverseCoupling(next) - inverseCoupling(current)
--     = - betaOne(current).
--
-- Bałaban describes this as a finite-difference approximation to the beta-flow.
-- The algebra below converts that orientation to the additive recursion used by
-- the repository.  It does not prove the physical coefficient or the uniform
-- remainder estimate.
------------------------------------------------------------------------

record FiniteDifferenceAlgebra (Scalar : Set) : Set₁ where
  field
    add subtract : Scalar → Scalar → Scalar
    negate : Scalar → Scalar

    differenceToAdd : ∀ next current increment →
      subtract next current ≡ increment →
      next ≡ add current increment

open FiniteDifferenceAlgebra public

record PrimaryInverseCouplingFiniteDifference
    (Scale Scalar : Set) : Set₁ where
  field
    algebra : FiniteDifferenceAlgebra Scalar
    nextScale : Scale → Scale

    inverseCoupling : Scale → Scalar
    betaOne : Scale → Scalar

    primaryFiniteDifference : ∀ scale →
      subtract algebra
        (inverseCoupling (nextScale scale))
        (inverseCoupling scale)
      ≡ negate algebra (betaOne scale)

open PrimaryInverseCouplingFiniteDifference public

primaryFiniteDifferenceAsAdditiveRecursion :
  ∀ {Scale Scalar : Set}
    (dataSet : PrimaryInverseCouplingFiniteDifference Scale Scalar)
    scale →
  inverseCoupling dataSet (nextScale dataSet scale)
  ≡ add (algebra dataSet)
      (inverseCoupling dataSet scale)
      (negate (algebra dataSet) (betaOne dataSet scale))
primaryFiniteDifferenceAsAdditiveRecursion dataSet scale =
  differenceToAdd (algebra dataSet)
    (inverseCoupling dataSet (nextScale dataSet scale))
    (inverseCoupling dataSet scale)
    (negate (algebra dataSet) (betaOne dataSet scale))
    (primaryFiniteDifference dataSet scale)

record PrimaryTheorem1AdmissibleFlow
    (Scale Coupling : Set) : Set₁ where
  field
    coupling : Scale → Coupling
    Admissible : Coupling → Set
    allScalesAdmissible : ∀ scale → Admissible (coupling scale)

    UVStable : Set
    primaryTheoremOneConclusion : UVStable

open PrimaryTheorem1AdmissibleFlow public

primaryBetaFiniteDifferenceOrientationLevel : ProofLevel
primaryBetaFiniteDifferenceOrientationLevel = standardImported

finiteDifferenceToAdditiveRecursionLevel : ProofLevel
finiteDifferenceToAdditiveRecursionLevel = machineChecked

primaryTheoremOneAdmissibleFlowArchitectureLevel : ProofLevel
primaryTheoremOneAdmissibleFlowArchitectureLevel = standardImported

physicalPrimaryBetaFunctionIdentificationInputsLevel : ProofLevel
physicalPrimaryBetaFunctionIdentificationInputsLevel = conditional

physicalPrimaryAdmissibleIntervalInputsLevel : ProofLevel
physicalPrimaryAdmissibleIntervalInputsLevel = conditional

physicalHRBetaRemainderUniformityInputsLevel : ProofLevel
physicalHRBetaRemainderUniformityInputsLevel = conditional
