module DASHI.Physics.Closure.NSTriadKNWeightedSchurDualityProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Gord Sinnamon.
-- Title: "Schur's Lemma and Best Constants in Weighted Norm Inequalities".
-- Venue/year: Le Matematiche LVII (2002), 185--204; author PDF dated 2003.
-- DOI: not listed in the cited publication metadata.
-- Uses: strong weighted forms of Schur's lemma, formal adjoints, converse
-- principles, and the applicability to non-negative matrix operators on
-- general measure spaces.
-- Relationship: gives the correct two-function replacement for matching
-- unweighted row and column constants. The concrete Navier-Stokes weight
-- pair and its cutoff-uniform estimates remain analytic obligations.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record DiscreteTwoWeightSchurCarrier
    {i j s x : Level} : Set (lsuc (i ⊔ j ⊔ s ⊔ x)) where
  field
    RowIndex : Set i
    ColumnIndex : Set j
    Scalar : Set s
    Vector : Set x

    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    squareRoot : Scalar → Scalar
    leq : Scalar → Scalar → Set s
    StrictlyPositive : Scalar → Set s

    kernelMagnitude : RowIndex → ColumnIndex → Scalar
    rowWeight : RowIndex → Scalar
    columnWeight : ColumnIndex → Scalar

    weightedRowSum : RowIndex → Scalar
    weightedColumnSum : ColumnIndex → Scalar
    rowConstant columnConstant : Scalar

    inputSquared outputSquared : Vector → Scalar

open DiscreteTwoWeightSchurCarrier public

record DiscreteTwoWeightSchurTheorem
    {i j s x : Level}
    (C : DiscreteTwoWeightSchurCarrier {i} {j} {s} {x}) :
    Set (lsuc (i ⊔ j ⊔ s ⊔ x)) where
  field
    rowWeightsPositive : ∀ row → StrictlyPositive C (rowWeight C row)
    columnWeightsPositive : ∀ column →
      StrictlyPositive C (columnWeight C column)

    weightedRowCondition : ∀ row →
      leq C
        (weightedRowSum C row)
        (multiply C (rowConstant C) (rowWeight C row))

    weightedColumnCondition : ∀ column →
      leq C
        (weightedColumnSum C column)
        (multiply C (columnConstant C) (columnWeight C column))

    weightedSchurOperatorBound : ∀ vector →
      leq C
        (outputSquared C vector)
        (multiply C
          (multiply C (rowConstant C) (columnConstant C))
          (inputSquared C vector))

    operatorNormBoundByGeometricMean : Set s

open DiscreteTwoWeightSchurTheorem public

record OneWeightSchurSpecialization
    {i s x : Level} : Set (lsuc (i ⊔ s ⊔ x)) where
  field
    Index : Set i
    Scalar : Set s
    Vector : Set x
    weight : Index → Scalar
    kernelMagnitude : Index → Index → Scalar
    weightedForwardCondition : Set s
    weightedTransposeCondition : Set s
    oneWeightOperatorBound : Set s

open OneWeightSchurSpecialization public

record SymmetricPartWeightedSchurBridge
    {i s : Level} : Set (lsuc (i ⊔ s)) where
  field
    Index : Set i
    Scalar : Set s
    RawKernel TransposeKernel SymmetricKernel : Index → Index → Scalar
    rawPlusTransposeIdentity : Set s
    rawWeightedRowBound : Set s
    transposeWeightedRowBound : Set s
    symmetricWeightedOperatorBound : Set s

open SymmetricPartWeightedSchurBridge public

record KiriukhinWeightSearchProgramme
    {i s : Level} : Set (lsuc (i ⊔ s)) where
  field
    Orbit : Set i
    Scalar : Set s
    orbitRadius : Orbit → Scalar

    kiriukhinRowProfile : Orbit → Scalar
    powerWeight : Nat → Orbit → Scalar
    dyadicPowerWeight : Nat → Orbit → Scalar

    CandidateWeightPair : Set s
    rowWeightOf : CandidateWeightPair → Orbit → Scalar
    columnWeightOf : CandidateWeightPair → Orbit → Scalar

    exactFiniteForwardConstant : CandidateWeightPair → Scalar
    exactFiniteDualConstant : CandidateWeightPair → Scalar
    exactFiniteSchurProduct : CandidateWeightPair → Scalar

    cutoffUniformForwardEstimate : CandidateWeightPair → Set s
    cutoffUniformDualEstimate : CandidateWeightPair → Set s
    candidateIndependentOfCutoff : CandidateWeightPair → Set s
    candidateCompatibleWithSevenClasses : CandidateWeightPair → Set s

open KiriukhinWeightSearchProgramme public

weightedSchurTheoremSurfaceRepresented : Bool
weightedSchurTheoremSurfaceRepresented = true

weightedSchurTheoremSurfaceRepresentedIsTrue :
  weightedSchurTheoremSurfaceRepresented ≡ true
weightedSchurTheoremSurfaceRepresentedIsTrue = refl

baselineWeightedColumnEstimateClosed : Bool
baselineWeightedColumnEstimateClosed = false

baselineWeightedColumnEstimateClosedIsFalse :
  baselineWeightedColumnEstimateClosed ≡ false
baselineWeightedColumnEstimateClosedIsFalse = refl
