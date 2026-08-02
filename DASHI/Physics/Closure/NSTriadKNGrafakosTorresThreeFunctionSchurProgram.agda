module DASHI.Physics.Closure.NSTriadKNGrafakosTorresThreeFunctionSchurProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
-- Uses: Theorem 1(c), the positive bilinear kernel, its two partial
-- adjoints, and three positive weight functions on the left, right, and
-- output index spaces.
-- Relationship: makes the three-function theorem the primary Stage-3
-- harmonic framework.  The linear two-function Schur test is retained only
-- as a frozen-output specialization.  No Kiriukhin orbit-shell
-- instantiation or cutoff-uniform Navier-Stokes estimate is imported.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record ThreeFunctionSchurCarrier
    {l r o s e : Level} : Set (lsuc (l ⊔ r ⊔ o ⊔ s ⊔ e)) where
  field
    LeftIndex : Set l
    RightIndex : Set r
    OutputIndex : Set o
    Scalar : Set s
    Exponent : Set e

    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    power : Scalar → Exponent → Scalar
    leq : Scalar → Scalar → Set s
    StrictlyPositive : Scalar → Set s

    p pConjugate q qConjugate rExponent rConjugate : Exponent
    holderBalance : Set e

    kernelMagnitude : OutputIndex → LeftIndex → RightIndex → Scalar

    leftWeight : LeftIndex → Scalar
    rightWeight : RightIndex → Scalar
    outputWeight : OutputIndex → Scalar
    schurConstant : Scalar

    outputWeightedSum : OutputIndex → Scalar
    leftPartialAdjointWeightedSum : LeftIndex → Scalar
    rightPartialAdjointWeightedSum : RightIndex → Scalar

    outputTarget : OutputIndex → Scalar
    leftTarget : LeftIndex → Scalar
    rightTarget : RightIndex → Scalar

open ThreeFunctionSchurCarrier public

record GrafakosTorresConditionC
    {l r o s e : Level}
    (C : ThreeFunctionSchurCarrier {l} {r} {o} {s} {e}) :
    Set (lsuc (l ⊔ r ⊔ o ⊔ s ⊔ e)) where
  field
    leftWeightPositive :
      ∀ left → StrictlyPositive C (leftWeight C left)
    rightWeightPositive :
      ∀ right → StrictlyPositive C (rightWeight C right)
    outputWeightPositive :
      ∀ output → StrictlyPositive C (outputWeight C output)

    outputCondition :
      ∀ output →
      leq C
        (outputWeightedSum C output)
        (multiply C (schurConstant C) (outputTarget C output))

    leftPartialAdjointCondition :
      ∀ left →
      leq C
        (leftPartialAdjointWeightedSum C left)
        (multiply C (schurConstant C) (leftTarget C left))

    rightPartialAdjointCondition :
      ∀ right →
      leq C
        (rightPartialAdjointWeightedSum C right)
        (multiply C (schurConstant C) (rightTarget C right))

    bilinearOperatorBound : Set s
    conditionCCharacterizesPositiveBoundedness : Set s

open GrafakosTorresConditionC public

record FrozenOutputTwoFunctionSpecialization
    {l r o s e : Level}
    (C : ThreeFunctionSchurCarrier {l} {r} {o} {s} {e}) :
    Set (lsuc (l ⊔ r ⊔ o ⊔ s ⊔ e)) where
  field
    distinguishedOutput : OutputIndex C
    everyOutputIdentifiedWithDistinguished :
      ∀ output → output ≡ distinguishedOutput
    outputWeightConstant :
      ∀ output →
      outputWeight C output ≡ outputWeight C distinguishedOutput

    outputConditionCollapsesToForwardRow : Set s
    leftAdjointCollapsesToWeightedColumn : Set s
    rightAdjointRedundantAfterFrozenLegIdentification : Set s
    resultingTwoFunctionSchurCriterion : Set s

open FrozenOutputTwoFunctionSpecialization public

record KiriukhinThreeFunctionInstantiationCutset
    {l r o s e : Level}
    (C : ThreeFunctionSchurCarrier {l} {r} {o} {s} {e}) :
    Set (lsuc (l ⊔ r ⊔ o ⊔ s ⊔ e)) where
  field
    rawOrbitTensorIdentified : Set s
    outputOrbitConventionMatched : Set s
    leftInputOrbitConventionMatched : Set s
    rightInputOrbitConventionMatched : Set s

    rawRowTheoremSuppliesOutputCondition : Set s
    firstPartialAdjointMajorantDerived : Set s
    secondPartialAdjointMajorantDerived : Set s

    threeDyadicWeightsSelected : Set s
    allThreeConditionsCutoffUniform : Set s
    directionWeightPreservesAllThreeConditions : Set s
    signedTriadAssemblyClosed : Set s

open KiriukhinThreeFunctionInstantiationCutset public

threeFunctionSchurPrimaryFramework : Bool
threeFunctionSchurPrimaryFramework = true

threeFunctionSchurPrimaryFrameworkIsTrue :
  threeFunctionSchurPrimaryFramework ≡ true
threeFunctionSchurPrimaryFrameworkIsTrue = refl

twoFunctionSchurRetainedAsFrozenOutputSpecialization : Bool
twoFunctionSchurRetainedAsFrozenOutputSpecialization = true

twoFunctionSchurRetainedAsFrozenOutputSpecializationIsTrue :
  twoFunctionSchurRetainedAsFrozenOutputSpecialization ≡ true
twoFunctionSchurRetainedAsFrozenOutputSpecializationIsTrue = refl

kiriukhinThreeFunctionInstantiationClosed : Bool
kiriukhinThreeFunctionInstantiationClosed = false

kiriukhinThreeFunctionInstantiationClosedIsFalse :
  kiriukhinThreeFunctionInstantiationClosed ≡ false
kiriukhinThreeFunctionInstantiationClosedIsFalse = refl
