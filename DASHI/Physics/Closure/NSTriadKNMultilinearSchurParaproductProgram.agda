module DASHI.Physics.Closure.NSTriadKNMultilinearSchurParaproductProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
-- Uses: Theorem 1(c), positive multilinear operators, three weight
-- functions, both partial adjoints, discrete trilinear forms, and multiplier
-- bounds on Sobolev and Besov spaces.
-- Relationship: the three-function theorem is the primary framework.  A
-- frozen-leg two-function row/column proof is only a specialization.
--
-- Author: Pierre Germain.
-- Title: "Multipliers, paramultipliers, and weak-strong uniqueness for the
-- Navier-Stokes equations".
-- Venue/year: Journal of Differential Equations 226 (2006), 373--428.
-- DOI: 10.1016/j.jde.2005.10.007.
-- Uses: boundedness of the Navier-Stokes trilinear functional, multiplier
-- and paramultiplier spaces, and the Bony low-high/high-low/remainder split.
-- Relationship: motivates class-dependent asymmetric estimates instead of
-- a forced symmetric unweighted row/column proof.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresThreeFunctionSchurProgram as ThreeFunction

data ParaproductGeometry : Set where
  near lowHigh highLow highHighToLow farLow farHigh transition residual :
    ParaproductGeometry

record PositiveMultilinearSchurCarrier
    {a b c s : Level} : Set (lsuc (a ⊔ b ⊔ c ⊔ s)) where
  field
    LeftIndex : Set a
    RightIndex : Set b
    OutputIndex : Set c
    Scalar : Set s

    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    leq : Scalar → Scalar → Set s
    StrictlyPositive : Scalar → Set s

    triadKernelMagnitude : OutputIndex → LeftIndex → RightIndex → Scalar
    resonance : OutputIndex → LeftIndex → RightIndex → Set

    leftWeight : LeftIndex → Scalar
    rightWeight : RightIndex → Scalar
    outputWeight : OutputIndex → Scalar

    multilinearOperatorValue : OutputIndex → Scalar
    leftPartialAdjointValue : LeftIndex → Scalar
    rightPartialAdjointValue : RightIndex → Scalar

open PositiveMultilinearSchurCarrier public

record PositiveMultilinearSchurTheorem
    {a b c s : Level}
    (C : PositiveMultilinearSchurCarrier {a} {b} {c} {s}) :
    Set (lsuc (a ⊔ b ⊔ c ⊔ s)) where
  field
    leftWeightPositive : ∀ left → StrictlyPositive C (leftWeight C left)
    rightWeightPositive : ∀ right → StrictlyPositive C (rightWeight C right)
    outputWeightPositive : ∀ output → StrictlyPositive C (outputWeight C output)

    outputSchurCondition : Set s
    leftPartialAdjointSchurCondition : Set s
    rightPartialAdjointSchurCondition : Set s
    discreteTrilinearFormBound : Set s

open PositiveMultilinearSchurTheorem public

record NavierStokesParaproductDualRoute
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff State : Set c
    Scalar : Set s
    add : Scalar → Scalar → Scalar
    leq : Scalar → Scalar → Set s

    fullTrilinearForm : Cutoff → State → State → State → Scalar
    classTrilinearForm :
      ParaproductGeometry → Cutoff → State → State → State → Scalar

    exactClassDecomposition : Set s
    lowHighDualBound : Set s
    highLowDualBound : Set s
    highHighToLowRemainderBound : Set s
    nearDiagonalBound : Set s
    farLowBound : Set s
    farHighBound : Set s
    transitionBound : Set s
    residualBound : Set s

    multiplierRouteClosed : Set s
    paramultiplierRouteClosed : Set s
    threeFunctionSchurRouteClosed : Set s
    classwiseDualTrilinearAssembly : Set s
    cutoffUniformTrilinearBound : Set s

open NavierStokesParaproductDualRoute public

data HarmonicFrameworkLevel : Set where
  primaryThreeFunction
  frozenOutputTwoFunction
  classwiseParaproductRealization : HarmonicFrameworkLevel

record Stage3HarmonicHierarchy : Set₁ where
  field
    primaryFramework :
      HarmonicFrameworkLevel
    primaryIsThreeFunction :
      primaryFramework ≡ primaryThreeFunction

    twoFunctionSpecializationAvailable :
      Set
    twoFunctionRequiresFrozenOutputLeg :
      Set

    outputConditionRequired :
      Set
    firstPartialAdjointConditionRequired :
      Set
    secondPartialAdjointConditionRequired :
      Set

    paraproductClassesRealizePartialAdjoints :
      Set
    noRawRowTheoremPromotedToThreeFunctionClosure :
      Set

open Stage3HarmonicHierarchy public

record BaselineColumnStrategyFork : Set₁ where
  field
    threeFunctionSchurAvailable : Set
    linearTwoWeightSpecializationAvailable : Set
    paraproductDualityAvailable : Set
    swapSymmetryAvailable : Set
    nullGainRedistributionAvailable : Set
    orbitCardinalityRenormalizationAvailable : Set

    selectedPrimaryStrategy : HarmonicFrameworkLevel
    selectionJustifiedByClasswiseEstimates : Set
    noFiniteCertificatePromotedToUniformTheorem : Set

open BaselineColumnStrategyFork public

threeFunctionFrameworkSubsumesFrozenLegSchur : Bool
threeFunctionFrameworkSubsumesFrozenLegSchur =
  ThreeFunction.twoFunctionSchurRetainedAsFrozenOutputSpecialization

threeFunctionFrameworkSubsumesFrozenLegSchurIsTrue :
  threeFunctionFrameworkSubsumesFrozenLegSchur ≡ true
threeFunctionFrameworkSubsumesFrozenLegSchurIsTrue =
  ThreeFunction.twoFunctionSchurRetainedAsFrozenOutputSpecializationIsTrue

multilinearAndParaproductRoutesRepresented : Bool
multilinearAndParaproductRoutesRepresented = true

multilinearAndParaproductRoutesRepresentedIsTrue :
  multilinearAndParaproductRoutesRepresented ≡ true
multilinearAndParaproductRoutesRepresentedIsTrue = refl

cutoffUniformDualTrilinearBoundClosed : Bool
cutoffUniformDualTrilinearBoundClosed = false

cutoffUniformDualTrilinearBoundClosedIsFalse :
  cutoffUniformDualTrilinearBoundClosed ≡ false
cutoffUniformDualTrilinearBoundClosedIsFalse = refl
