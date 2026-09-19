{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteBoundaryConditionedDobrushinExact where

------------------------------------------------------------------------
-- CORRECT FINITE DOBRUSHIN OBJECT FOR THE RG GOOD REGION
--
-- The coarse projection is held fixed.  The varying parameter is a remote
-- boundary/source condition.  Each boundary condition supplies a raw positive
-- weight on the SAME finite local fibre and a normalising scalar.
--
-- If changing the remote boundary changes the raw local weight relatively by
--
--   |u_eta(y)-u_xi(y)| <= epsilon * u_eta(y),
--
-- then the normalised local conditional rows differ in L1 by at most 2 epsilon.
-- Hence every local observable |f| <= A changes by at most 2 A epsilon.
--
-- This is the finite Gibbs/Dobrushin compiler required by S1.  It deliberately
-- does NOT compare reopening rows belonging to different exact coarse fibres.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteDobrushinReopeningExact as Dobrushin
import DASHI.Physics.YangMills.BalabanFiniteNormalizedWeightDobrushinExact as Normalize
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record BoundaryConditionedFiniteFibre
    (Local Boundary : Set) : Set₁ where
  field
    localStates : List Local

    rawWeight : Boundary → Local → ℚ
    normalizer : Boundary → ℚ

    rawWeightNonnegative : ∀ boundary local →
      0ℚ ≤ rawWeight boundary local
    normalizerNonnegative : ∀ boundary →
      0ℚ ≤ normalizer boundary

    normalized : ∀ boundary →
      normalizer boundary
      * DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRational
          localStates (rawWeight boundary)
      ≡ 1ℚ

open BoundaryConditionedFiniteFibre public

import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

conditionalRow :
  ∀ {Local Boundary} →
  BoundaryConditionedFiniteFibre Local Boundary →
  Boundary → Local → ℚ
conditionalRow dataSet boundary local =
  normalizer dataSet boundary * rawWeight dataSet boundary local

boundaryPair :
  ∀ {Local Boundary}
    (dataSet : BoundaryConditionedFiniteFibre Local Boundary)
    (left right : Boundary) →
  Normalize.NormalizedFiniteWeightPair Local
boundaryPair dataSet left right = record
  { Normalize.NormalizedFiniteWeightPair.states = localStates dataSet
  ; Normalize.NormalizedFiniteWeightPair.leftRaw = rawWeight dataSet left
  ; Normalize.NormalizedFiniteWeightPair.rightRaw = rawWeight dataSet right
  ; Normalize.NormalizedFiniteWeightPair.leftNormalizer = normalizer dataSet left
  ; Normalize.NormalizedFiniteWeightPair.rightNormalizer = normalizer dataSet right
  ; Normalize.NormalizedFiniteWeightPair.leftRawNonnegative =
      rawWeightNonnegative dataSet left
  ; Normalize.NormalizedFiniteWeightPair.rightRawNonnegative =
      rawWeightNonnegative dataSet right
  ; Normalize.NormalizedFiniteWeightPair.leftNormalizerNonnegative =
      normalizerNonnegative dataSet left
  ; Normalize.NormalizedFiniteWeightPair.rightNormalizerNonnegative =
      normalizerNonnegative dataSet right
  ; Normalize.NormalizedFiniteWeightPair.leftNormalized =
      normalized dataSet left
  ; Normalize.NormalizedFiniteWeightPair.rightNormalized =
      normalized dataSet right
  }

record RelativeBoundaryWeightInfluence
    {Local Boundary : Set}
    (dataSet : BoundaryConditionedFiniteFibre Local Boundary)
    (left right : Boundary) : Set₁ where
  field
    epsilon : ℚ
    epsilonNonnegative : 0ℚ ≤ epsilon

    rawRelativeInfluence : ∀ local →
      ∣ rawWeight dataSet left local - rawWeight dataSet right local ∣
      ≤ epsilon * rawWeight dataSet left local

open RelativeBoundaryWeightInfluence public

asRelativeRawWeightPerturbation :
  ∀ {Local Boundary}
    {dataSet : BoundaryConditionedFiniteFibre Local Boundary}
    {left right : Boundary} →
  RelativeBoundaryWeightInfluence dataSet left right →
  Normalize.RelativeRawWeightPerturbation
    (boundaryPair dataSet left right)
asRelativeRawWeightPerturbation influence = record
  { Normalize.RelativeRawWeightPerturbation.epsilon = epsilon influence
  ; Normalize.RelativeRawWeightPerturbation.epsilonNonnegative =
      epsilonNonnegative influence
  ; Normalize.RelativeRawWeightPerturbation.pointwiseRelativeDifference =
      rawRelativeInfluence influence
  }

conditionalRowL1 :
  ∀ {Local Boundary}
    (dataSet : BoundaryConditionedFiniteFibre Local Boundary) →
  Boundary → Boundary → ℚ
conditionalRowL1 dataSet left right =
  Dobrushin.rowL1Difference
    (localStates dataSet)
    (conditionalRow dataSet left)
    (conditionalRow dataSet right)

relativeBoundaryInfluenceImpliesRowL1 :
  ∀ {Local Boundary}
    {dataSet : BoundaryConditionedFiniteFibre Local Boundary}
    {left right : Boundary}
    (influence : RelativeBoundaryWeightInfluence dataSet left right) →
  conditionalRowL1 dataSet left right
  ≤ (1ℚ + 1ℚ) * epsilon influence
relativeBoundaryInfluenceImpliesRowL1
    {dataSet = dataSet} {left} {right} influence =
  Normalize.normalizedRowL1BelowTwiceRelativePerturbation
    (asRelativeRawWeightPerturbation influence)

conditionalExpectation :
  ∀ {Local Boundary} →
  BoundaryConditionedFiniteFibre Local Boundary →
  (Local → ℚ) → Boundary → ℚ
conditionalExpectation dataSet observable boundary =
  Sums.sumRational (localStates dataSet)
    (λ local → conditionalRow dataSet boundary local * observable local)

relativeBoundaryInfluenceImpliesExpectationOscillation :
  ∀ {Local Boundary}
    {dataSet : BoundaryConditionedFiniteFibre Local Boundary}
    {left right : Boundary}
    (influence : RelativeBoundaryWeightInfluence dataSet left right)
    (observable : Local → ℚ)
    majorant →
  0ℚ ≤ majorant →
  (∀ local → ∣ observable local ∣ ≤ majorant) →
  ∣ conditionalExpectation dataSet observable left
    - conditionalExpectation dataSet observable right ∣
  ≤
  majorant * ((1ℚ + 1ℚ) * epsilon influence)
relativeBoundaryInfluenceImpliesExpectationOscillation
    {dataSet = dataSet} {left} {right}
    influence observable majorant majorantNN bounded =
  let
    raw =
      Dobrushin.finiteExpectationRowDifferenceBound
        (localStates dataSet)
        (conditionalRow dataSet left)
        (conditionalRow dataSet right)
        observable majorant majorantNN bounded

    rowBound =
      relativeBoundaryInfluenceImpliesRowL1 influence

    twoEpsilonNN : 0ℚ ≤ (1ℚ + 1ℚ) * epsilon influence
    twoEpsilonNN =
      let
        twoNN : 0ℚ ≤ 1ℚ + 1ℚ
        twoNN = DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact.baseBelowBasePlusRemainder
          0ℚ (1ℚ + 1ℚ) (Data.Rational.Properties.+-mono-≤ Data.Rational.Properties.0≤1 Data.Rational.Properties.0≤1)
      in
      Norm.productNonnegative
        (1ℚ + 1ℚ) (epsilon influence)
        twoNN (epsilonNonnegative influence)
  in
  Data.Rational.Properties.≤-trans raw
    (Norm.scaleNonnegative majorant majorantNN rowBound)

boundaryConditionedNormalizationStabilityLevel : ProofLevel
boundaryConditionedNormalizationStabilityLevel = machineChecked

boundaryConditionedDobrushinExpectationLevel : ProofLevel
boundaryConditionedDobrushinExpectationLevel = machineChecked
