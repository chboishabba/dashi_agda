module DASHI.Physics.Closure.NSTriadKNRetainedPositiveSectorKernelOperator where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Nat using (_≤_; z≤n)

import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierTriadCarrier as Rich
import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Finite weighted folds.
------------------------------------------------------------------------

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (x ∷ xs) = x + sumNat xs

weightedFold :
  {A : Set} →
  (A → Nat) →
  List A → Nat
weightedFold weight xs = sumNat (map weight xs)

------------------------------------------------------------------------
-- Physical retained-positive-sector fiber data.
--
-- Unlike the legacy proxy, every incidence is mapped to an actual retained
-- Fourier triad.  The fiber is finite by construction, and completeness is a
-- theorem field rather than an untyped closure flag.
------------------------------------------------------------------------

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

record RetainedPositiveSectorFiberData : Set₁ where
  constructor mkRetainedPositiveSectorFiberData
  field
    Index : Set
    TriadIncidence : Set

    sourceIndex : TriadIncidence → Index
    targetIndex : TriadIncidence → Index
    retainedTriad : TriadIncidence → Rich.RetainedTriad
    retainedPositiveSector : TriadIncidence → Set
    triadWeight : TriadIncidence → Nat

    fiber : Index → Index → List TriadIncidence

    fiberSourceAgreement :
      {i j : Index} →
      (τ : TriadIncidence) →
      τ ∈ fiber i j →
      sourceIndex τ ≡ i

    fiberTargetAgreement :
      {i j : Index} →
      (τ : TriadIncidence) →
      τ ∈ fiber i j →
      targetIndex τ ≡ j

    fiberRetainedAgreement :
      {i j : Index} →
      (τ : TriadIncidence) →
      τ ∈ fiber i j →
      retainedPositiveSector τ

    fiberComplete :
      {i j : Index} →
      (τ : TriadIncidence) →
      sourceIndex τ ≡ i →
      targetIndex τ ≡ j →
      retainedPositiveSector τ →
      τ ∈ fiber i j

open RetainedPositiveSectorFiberData public

retainedFiberAggregate :
  (data : RetainedPositiveSectorFiberData) →
  RetainedPositiveSectorFiberData.Index data →
  RetainedPositiveSectorFiberData.Index data →
  Nat
retainedFiberAggregate data i j =
  weightedFold
    (RetainedPositiveSectorFiberData.triadWeight data)
    (RetainedPositiveSectorFiberData.fiber data i j)

retainedFiberAggregateIsFiniteWeightedSum :
  (data : RetainedPositiveSectorFiberData) →
  (i j : RetainedPositiveSectorFiberData.Index data) →
  retainedFiberAggregate data i j
    ≡ weightedFold
        (RetainedPositiveSectorFiberData.triadWeight data)
        (RetainedPositiveSectorFiberData.fiber data i j)
retainedFiberAggregateIsFiniteWeightedSum data i j = refl

------------------------------------------------------------------------
-- Construct the physical kernel-formula target from the retained fiber.
------------------------------------------------------------------------

retainedFiberToKernelFormulaTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (data : RetainedPositiveSectorFiberData) →
  KernelFormula.ActualPairIncidenceKernelFormulaTarget
    residueNormModel
    (suc zero)
retainedFiberToKernelFormulaTarget residueNormModel data =
  KernelFormula.mkActualPairIncidenceKernelFormulaTarget
    (RetainedPositiveSectorFiberData.Index data)
    (RetainedPositiveSectorFiberData.Index data)
    (RetainedPositiveSectorFiberData.TriadIncidence data)
    (RetainedPositiveSectorFiberData.sourceIndex data)
    (RetainedPositiveSectorFiberData.targetIndex data)
    (RetainedPositiveSectorFiberData.retainedPositiveSector data)
    (RetainedPositiveSectorFiberData.triadWeight data)
    enumeration
    (retainedFiberAggregate data)
    (λ i j → refl)
    (λ i j → z≤n)
  where
  enumeration :
    KernelFormula.RetainedTriadFiberEnumerationInputs
      (RetainedPositiveSectorFiberData.Index data)
      (RetainedPositiveSectorFiberData.Index data)
      (RetainedPositiveSectorFiberData.TriadIncidence data)
      (RetainedPositiveSectorFiberData.sourceIndex data)
      (RetainedPositiveSectorFiberData.targetIndex data)
      (RetainedPositiveSectorFiberData.retainedPositiveSector data)
      (RetainedPositiveSectorFiberData.triadWeight data)
  enumeration =
    KernelFormula.mkRetainedTriadFiberEnumerationInputs
      (RetainedPositiveSectorFiberData.fiber data)
      (RetainedPositiveSectorFiberData.fiberSourceAgreement data)
      (RetainedPositiveSectorFiberData.fiberTargetAgreement data)
      (RetainedPositiveSectorFiberData.fiberRetainedAgreement data)
      (RetainedPositiveSectorFiberData.fiberComplete data)
      (retainedFiberAggregate data)
      (λ i j → refl)

------------------------------------------------------------------------
-- A finite matrix carrier and its exact operator action.
------------------------------------------------------------------------

record FiniteRetainedStage3MatrixInputs
    (admissibility : Rich.FourierTriadAdmissibilityInputs) : Set₁ where
  constructor mkFiniteRetainedStage3MatrixInputs
  field
    fiberData : RetainedPositiveSectorFiberData

    indexEnumeration :
      List (RetainedPositiveSectorFiberData.Index fiberData)

    indexEnumerationComplete :
      (i : RetainedPositiveSectorFiberData.Index fiberData) →
      i ∈ indexEnumeration

    State : Set
    coefficientAt :
      State → RetainedPositiveSectorFiberData.Index fiberData → Nat

    rebuildState :
      (RetainedPositiveSectorFiberData.Index fiberData → Nat) → State

    coefficientAfterRebuild :
      (a : RetainedPositiveSectorFiberData.Index fiberData → Nat) →
      (i : RetainedPositiveSectorFiberData.Index fiberData) →
      coefficientAt (rebuildState a) i ≡ a i

    stateRealization :
      State → Rich.AdmissibleFourierTriadState admissibility

    qBase : State → Nat
    strongNormSquared : State → Nat
    residueEnergy : State → Nat

    forgetToEnergy :
      State → ResidueNorm.ResidueEnergyCarrier (suc zero)

    forgetPreservesEnergy :
      (x : State) →
      ResidueNorm.residueEnergy (forgetToEnergy x) ≡ residueEnergy x

open FiniteRetainedStage3MatrixInputs public

matrixEntry :
  {admissibility : Rich.FourierTriadAdmissibilityInputs} →
  (inputs : FiniteRetainedStage3MatrixInputs admissibility) →
  RetainedPositiveSectorFiberData.Index (fiberData inputs) →
  RetainedPositiveSectorFiberData.Index (fiberData inputs) →
  Nat
matrixEntry inputs = retainedFiberAggregate (fiberData inputs)

matrixRowAction :
  {admissibility : Rich.FourierTriadAdmissibilityInputs} →
  (inputs : FiniteRetainedStage3MatrixInputs admissibility) →
  (x : FiniteRetainedStage3MatrixInputs.State inputs) →
  RetainedPositiveSectorFiberData.Index (fiberData inputs) →
  Nat
matrixRowAction inputs x i =
  weightedFold
    (λ j → matrixEntry inputs i j * coefficientAt inputs x j)
    (indexEnumeration inputs)

stage3OperatorAction :
  {admissibility : Rich.FourierTriadAdmissibilityInputs} →
  (inputs : FiniteRetainedStage3MatrixInputs admissibility) →
  FiniteRetainedStage3MatrixInputs.State inputs →
  FiniteRetainedStage3MatrixInputs.State inputs
stage3OperatorAction inputs x =
  rebuildState inputs (matrixRowAction inputs x)

stage3Pairing :
  {admissibility : Rich.FourierTriadAdmissibilityInputs} →
  (inputs : FiniteRetainedStage3MatrixInputs admissibility) →
  FiniteRetainedStage3MatrixInputs.State inputs →
  FiniteRetainedStage3MatrixInputs.State inputs →
  Nat
stage3Pairing inputs x y =
  weightedFold
    (λ i → coefficientAt inputs x i * coefficientAt inputs y i)
    (indexEnumeration inputs)

stage3QuadraticError :
  {admissibility : Rich.FourierTriadAdmissibilityInputs} →
  (inputs : FiniteRetainedStage3MatrixInputs admissibility) →
  FiniteRetainedStage3MatrixInputs.State inputs → Nat
stage3QuadraticError inputs x =
  stage3Pairing inputs (stage3OperatorAction inputs x) x

operatorRealizesRetainedFiberMatrix :
  {admissibility : Rich.FourierTriadAdmissibilityInputs} →
  (inputs : FiniteRetainedStage3MatrixInputs admissibility) →
  (x : FiniteRetainedStage3MatrixInputs.State inputs) →
  (i : RetainedPositiveSectorFiberData.Index (fiberData inputs)) →
  coefficientAt inputs (stage3OperatorAction inputs x) i
    ≡ weightedFold
        (λ j → matrixEntry inputs i j * coefficientAt inputs x j)
        (indexEnumeration inputs)
operatorRealizesRetainedFiberMatrix inputs x i =
  coefficientAfterRebuild inputs (matrixRowAction inputs x) i

qErrorIsRetainedOperatorQuadraticForm :
  {admissibility : Rich.FourierTriadAdmissibilityInputs} →
  (inputs : FiniteRetainedStage3MatrixInputs admissibility) →
  (x : FiniteRetainedStage3MatrixInputs.State inputs) →
  stage3QuadraticError inputs x
    ≡ stage3Pairing inputs (stage3OperatorAction inputs x) x
qErrorIsRetainedOperatorQuadraticForm inputs x = refl

finiteRetainedInputsToRichOperator :
  {admissibility : Rich.FourierTriadAdmissibilityInputs} →
  (inputs : FiniteRetainedStage3MatrixInputs admissibility) →
  Rich.RichStage3PairIncidenceOperator admissibility
finiteRetainedInputsToRichOperator inputs =
  Rich.mkRichStage3PairIncidenceOperator
    (FiniteRetainedStage3MatrixInputs.State inputs)
    (FiniteRetainedStage3MatrixInputs.stateRealization inputs)
    (RetainedPositiveSectorFiberData.Index
      (FiniteRetainedStage3MatrixInputs.fiberData inputs))
    (λ _ → zero)
    (matrixEntry inputs)
    (FiniteRetainedStage3MatrixInputs.coefficientAt inputs)
    (stage3OperatorAction inputs)
    (stage3Pairing inputs)
    (FiniteRetainedStage3MatrixInputs.qBase inputs)
    (stage3QuadraticError inputs)
    (FiniteRetainedStage3MatrixInputs.strongNormSquared inputs)
    ((x : FiniteRetainedStage3MatrixInputs.State inputs) →
      (i : RetainedPositiveSectorFiberData.Index
        (FiniteRetainedStage3MatrixInputs.fiberData inputs)) →
      coefficientAt inputs (stage3OperatorAction inputs x) i
        ≡ matrixRowAction inputs x i)
    (qErrorIsRetainedOperatorQuadraticForm inputs)
    (FiniteRetainedStage3MatrixInputs.residueEnergy inputs)
    (FiniteRetainedStage3MatrixInputs.forgetToEnergy inputs)
    (FiniteRetainedStage3MatrixInputs.forgetPreservesEnergy inputs)

------------------------------------------------------------------------
-- Audit gates.
------------------------------------------------------------------------

retainedPositiveSectorFiberConstructionImplemented : Bool
retainedPositiveSectorFiberConstructionImplemented = true

retainedPositiveSectorFiberConstructionImplementedIsTrue :
  retainedPositiveSectorFiberConstructionImplemented ≡ true
retainedPositiveSectorFiberConstructionImplementedIsTrue = refl

finiteWeightedAggregateImplemented : Bool
finiteWeightedAggregateImplemented = true

finiteWeightedAggregateImplementedIsTrue :
  finiteWeightedAggregateImplemented ≡ true
finiteWeightedAggregateImplementedIsTrue = refl

retainedFiberToRichOperatorImplemented : Bool
retainedFiberToRichOperatorImplemented = true

retainedFiberToRichOperatorImplementedIsTrue :
  retainedFiberToRichOperatorImplemented ≡ true
retainedFiberToRichOperatorImplementedIsTrue = refl

-- The generic construction is now complete.  The remaining physical input is a
-- concrete inhabitant whose incidences carry the repository's actual Fourier
-- modes and whose fiber completeness theorem is derived from the class-specific
-- incidence enumerators rather than asserted externally.
canonicalPhysicalRetainedFiberInhabited : Bool
canonicalPhysicalRetainedFiberInhabited = false

canonicalPhysicalRetainedFiberInhabitedIsFalse :
  canonicalPhysicalRetainedFiberInhabited ≡ false
canonicalPhysicalRetainedFiberInhabitedIsFalse = refl
