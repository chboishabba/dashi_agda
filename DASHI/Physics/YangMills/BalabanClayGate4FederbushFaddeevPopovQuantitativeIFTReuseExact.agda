module DASHI.Physics.YangMills.BalabanClayGate4FederbushFaddeevPopovQuantitativeIFTReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageImplicitDerivativeExact as Federbush
import DASHI.Physics.YangMills.BalabanClayGate4TreeBackgroundSliceTransitionExact as Slice

------------------------------------------------------------------------
-- One quantitative theorem, two physical applications.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- The Federbush centre equation and the background-gauge condition are both
-- local equations on finite-dimensional carriers.  This module forces both to
-- pass through the same invariant-ball/contraction and relative-inverse data,
-- so no second implicit-function theorem can silently use different radius or
-- inverse conventions.
------------------------------------------------------------------------

record FederbushQuantitativeClosure
    (Input Centre Residual Bound : Set) : Set₁ where
  field
    implicitFunction :
      Quantitative.QuantitativeImplicitFunctionData Input Centre Bound

    differential :
      Federbush.FederbushImplicitDifferential Input Centre Residual

    physicalDifferential :
      Federbush.PhysicalFederbushAverageDerivative Input Centre Residual

    physicalDifferentialUsesSelectedData :
      Federbush.implicitData physicalDifferential ≡ differential

    QuantitativeResidualIsFederbushEquation : Set
    quantitativeResidualIsFederbushEquation :
      QuantitativeResidualIsFederbushEquation

open FederbushQuantitativeClosure public

federbushAverageUniqueOnQuantitativeBall :
  ∀ {Input Centre Residual Bound}
    (closure : FederbushQuantitativeClosure
      Input Centre Residual Bound)
    input
    (admissible : Quantitative.AdmissibleInput
      (implicitFunction closure) input)
    candidate →
  Quantitative.InBall
    (Quantitative.contractionBall (implicitFunction closure) input)
    candidate →
  Quantitative.ResidualZero (implicitFunction closure) input candidate →
  candidate ≡ Quantitative.implicitSolution
    (implicitFunction closure) input admissible
federbushAverageUniqueOnQuantitativeBall closure =
  Quantitative.residualSolutionUniqueInQuantitativeBall
    (implicitFunction closure)

federbushPhysicalDerivativeUsesImplicitFormula :
  ∀ {Input Centre Residual Bound}
    (closure : FederbushQuantitativeClosure
      Input Centre Residual Bound)
    input →
  Federbush.physicalDerivative (physicalDifferential closure) input
  ≡ Federbush.implicitAverageDerivative (differential closure) input
federbushPhysicalDerivativeUsesImplicitFormula closure input
  rewrite physicalDifferentialUsesSelectedData closure =
  Federbush.physicalAverageDerivativeEqualsImplicitFormula
    (physicalDifferential closure) input

record BackgroundSliceQuantitativeClosure
    (TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound : Set)
    : Set₁ where
  field
    implicitFunction :
      Quantitative.QuantitativeImplicitFunctionData
        TreeSlice BackgroundSlice Bound

    transition : Slice.LocalSliceTransition
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent

    implicitSolutionIsTransition : ∀ tree
      (admissible : Quantitative.AdmissibleInput implicitFunction tree) →
      Quantitative.implicitSolution implicitFunction tree admissible
      ≡ Slice.toBackground transition tree

    QuantitativeResidualIsBackgroundGaugeCondition : Set
    quantitativeResidualIsBackgroundGaugeCondition :
      QuantitativeResidualIsBackgroundGaugeCondition

open BackgroundSliceQuantitativeClosure public

backgroundSliceUniqueOnQuantitativeBall :
  ∀ {TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound}
    (closure : BackgroundSliceQuantitativeClosure
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound)
    tree
    (admissible : Quantitative.AdmissibleInput
      (implicitFunction closure) tree)
    candidate →
  Quantitative.InBall
    (Quantitative.contractionBall (implicitFunction closure) tree)
    candidate →
  Quantitative.ResidualZero (implicitFunction closure) tree candidate →
  candidate ≡ Slice.toBackground (transition closure) tree
backgroundSliceUniqueOnQuantitativeBall closure tree admissible candidate
    candidateIn candidateResidual =
  trans
    (Quantitative.residualSolutionUniqueInQuantitativeBall
      (implicitFunction closure) tree admissible candidate
      candidateIn candidateResidual)
    (implicitSolutionIsTransition closure tree admissible)

record SharedQuantitativeIFTApplications
    (FederbushInput FederbushCentre FederbushResidual
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound : Set)
    : Set₁ where
  field
    federbush : FederbushQuantitativeClosure
      FederbushInput FederbushCentre FederbushResidual Bound

    backgroundSlice : BackgroundSliceQuantitativeClosure
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent Bound

    federbushRadiusBudget backgroundSliceRadiusBudget :
      Quantitative.QuantitativeRadiusBudget Bound

    CommonNormAndScalarConvention : Set
    commonNormAndScalarConvention : CommonNormAndScalarConvention

open SharedQuantitativeIFTApplications public

federbushQuantitativeUniquenessAssemblyLevel : ProofLevel
federbushQuantitativeUniquenessAssemblyLevel = machineChecked

federbushImplicitDerivativeReuseLevel : ProofLevel
federbushImplicitDerivativeReuseLevel = machineChecked

backgroundSliceQuantitativeUniquenessAssemblyLevel : ProofLevel
backgroundSliceQuantitativeUniquenessAssemblyLevel = machineChecked

sharedFederbushFaddeevPopovIFTArchitectureLevel : ProofLevel
sharedFederbushFaddeevPopovIFTArchitectureLevel = machineChecked

physicalFederbushRadiusAndLipschitzInputsLevel : ProofLevel
physicalFederbushRadiusAndLipschitzInputsLevel = conditional

physicalFaddeevPopovRadiusAndLipschitzInputsLevel : ProofLevel
physicalFaddeevPopovRadiusAndLipschitzInputsLevel = conditional

physicalSharedNormConventionInputsLevel : ProofLevel
physicalSharedNormConventionInputsLevel = conditional
