module DASHI.Physics.YangMills.BalabanClayGate4FederbushFaddeevPopovInverseStabilityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative

------------------------------------------------------------------------
-- Shared finite-dimensional inverse stability.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- If the normalized perturbation has relative norm q < 1, the common theorem
-- proves the kernel is trivial.  On a finite square carrier, trivial kernel is
-- upgraded to a two-sided inverse.  The Federbush centre differential and the
-- Faddeev--Popov operator therefore differ only in the physical construction of
-- their defect map and q-bound.
------------------------------------------------------------------------

record RelativeFiniteInverseClosure
    (Vector Bound : Set) : Set₁ where
  field
    relativeKernel : Quantitative.RelativeInverseKernelData Vector Bound

    finiteSquare : Quantitative.FiniteSquareInverseUpgrade
      Vector (Quantitative.operator relativeKernel)

    kernelAgreement : ∀ vector →
      Quantitative.Kernel finiteSquare vector
      ≡ Quantitative.Kernel relativeKernel vector

open RelativeFiniteInverseClosure public

upgradeKernelTrivial :
  ∀ {Vector Bound}
    (closure : RelativeFiniteInverseClosure Vector Bound)
    vector →
  Quantitative.Kernel (finiteSquare closure) vector →
  vector ≡ Quantitative.zeroVector (relativeKernel closure)
upgradeKernelTrivial closure vector kernel =
  Quantitative.relativeInverseKernelTrivial
    (relativeKernel closure) vector
    (subst (λ proposition → proposition)
      (kernelAgreement closure vector) kernel)

record ZeroConventionAgreement
    {Vector Bound : Set}
    (closure : RelativeFiniteInverseClosure Vector Bound) : Set where
  field
    zeroConvention :
      Quantitative.zeroVector (finiteSquare closure)
      ≡ Quantitative.zeroVector (relativeKernel closure)

open ZeroConventionAgreement public

upgradeKernelTrivialInFiniteConvention :
  ∀ {Vector Bound}
    (closure : RelativeFiniteInverseClosure Vector Bound)
    (agreement : ZeroConventionAgreement closure)
    vector →
  Quantitative.Kernel (finiteSquare closure) vector →
  vector ≡ Quantitative.zeroVector (finiteSquare closure)
upgradeKernelTrivialInFiniteConvention closure agreement vector kernel =
  subst
    (λ selectedZero → vector ≡ selectedZero)
    (symmetry (zeroConvention agreement))
    (upgradeKernelTrivial closure vector kernel)
  where
  symmetry : ∀ {A : Set} {left right : A} →
    left ≡ right → right ≡ left
  symmetry Agda.Builtin.Equality.refl = Agda.Builtin.Equality.refl

relativeFiniteInverseLeftLaw :
  ∀ {Vector Bound}
    (closure : RelativeFiniteInverseClosure Vector Bound)
    (agreement : ZeroConventionAgreement closure) →
  ∀ vector →
  Quantitative.inverse (finiteSquare closure)
    (Quantitative.operator (relativeKernel closure) vector)
  ≡ vector
relativeFiniteInverseLeftLaw closure agreement =
  Quantitative.inverseFromTrivialKernel (finiteSquare closure)
    (upgradeKernelTrivialInFiniteConvention closure agreement)

relativeFiniteInverseRightLaw :
  ∀ {Vector Bound}
    (closure : RelativeFiniteInverseClosure Vector Bound)
    (agreement : ZeroConventionAgreement closure) →
  ∀ vector →
  Quantitative.operator (relativeKernel closure)
    (Quantitative.inverse (finiteSquare closure) vector)
  ≡ vector
relativeFiniteInverseRightLaw closure agreement =
  Quantitative.operatorAfterInverseFromTrivialKernel (finiteSquare closure)
    (upgradeKernelTrivialInFiniteConvention closure agreement)

record FederbushCentreInverseClosure
    (CentreTangent Bound : Set) : Set₁ where
  field
    closure : RelativeFiniteInverseClosure CentreTangent Bound
    CentreDerivativeIsSelectedOperator : Set
    centreDerivativeIsSelectedOperator : CentreDerivativeIsSelectedOperator

open FederbushCentreInverseClosure public

record FaddeevPopovInverseClosure
    (GaugeParameter Bound : Set) : Set₁ where
  field
    closure : RelativeFiniteInverseClosure GaugeParameter Bound
    FaddeevPopovOperatorIsSelectedOperator : Set
    faddeevPopovOperatorIsSelectedOperator :
      FaddeevPopovOperatorIsSelectedOperator

open FaddeevPopovInverseClosure public

relativeFiniteInverseKernelUpgradeLevel : ProofLevel
relativeFiniteInverseKernelUpgradeLevel = machineChecked

relativeFiniteTwoSidedInverseAssemblyLevel : ProofLevel
relativeFiniteTwoSidedInverseAssemblyLevel = machineChecked

sharedFederbushFaddeevPopovInverseArchitectureLevel : ProofLevel
sharedFederbushFaddeevPopovInverseArchitectureLevel = machineChecked

physicalFederbushCentreRelativeDefectInputsLevel : ProofLevel
physicalFederbushCentreRelativeDefectInputsLevel = conditional

physicalFaddeevPopovRelativeDefectInputsLevel : ProofLevel
physicalFaddeevPopovRelativeDefectInputsLevel = conditional

physicalFiniteSquareCarrierIdentificationInputsLevel : ProofLevel
physicalFiniteSquareCarrierIdentificationInputsLevel = conditional
