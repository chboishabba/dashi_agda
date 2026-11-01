module DASHI.Physics.Closure.NSTriadKNLuoRationalLerayMultiplierContractiveExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the rational finite-dimensional core of the periodic Leray multiplier
-- estimate rather than accepting projection contractivity as a producer.
-- For a nonzero wave vector k and inverse squared length i satisfying
--
--   i |k|^2 = 1,
--
-- the orthogonal projection P_k v = v - i (k dot v) k obeys the exact
-- Pythagorean identity
--
--   |P_k v|^2 + i (k dot v)^2 = |v|^2,
--
-- hence |P_k v|^2 <= |v|^2.  Finite Cauchy--Schwarz then proves
--
--   |P_k (k dot F)|^2 <= |k|^2 |F|^2
--
-- for real and complex rational 3x3 tensors.  This is the exact algebraic
-- content of HH-P4.  Identifying these rational vectors with actual torus
-- Fourier coefficients remains the constructive-real/analytic bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record Vec3 : Set where
  constructor vec3
  field
    vx vy vz : ℚ

open Vec3 public

vecAdd : Vec3 → Vec3 → Vec3
vecAdd a b =
  vec3
    (vx a + vx b)
    (vy a + vy b)
    (vz a + vz b)

vecScale : ℚ → Vec3 → Vec3
vecScale scalar value =
  vec3
    (scalar * vx value)
    (scalar * vy value)
    (scalar * vz value)

vecSubtract : Vec3 → Vec3 → Vec3
vecSubtract a b =
  vec3
    (vx a - vx b)
    (vy a - vy b)
    (vz a - vz b)

vecDot : Vec3 → Vec3 → ℚ
vecDot a b =
  vx a * vx b + vy a * vy b + vz a * vz b

vecNormSquared : Vec3 → ℚ
vecNormSquared value = vecDot value value

record RationalLerayData : Set where
  constructor rational-leray-data
  field
    wave value : Vec3
    inverseWaveNormSquared : ℚ
    inverseNonnegative : 0ℚ ≤ inverseWaveNormSquared
    inverseCalibration :
      inverseWaveNormSquared * vecNormSquared wave ≡ 1ℚ

open RationalLerayData public

projectionCoefficient : RationalLerayData → ℚ
projectionCoefficient dataSet =
  inverseWaveNormSquared dataSet
    * vecDot (wave dataSet) (value dataSet)

lerayProject : RationalLerayData → Vec3
lerayProject dataSet =
  vecSubtract
    (value dataSet)
    (vecScale (projectionCoefficient dataSet) (wave dataSet))

projectionDefect : RationalLerayData → ℚ
projectionDefect dataSet =
  inverseWaveNormSquared dataSet
  * L2.square (vecDot (wave dataSet) (value dataSet))

projectionExpansion :
  (dataSet : RationalLerayData) →
  vecNormSquared (lerayProject dataSet)
    + projectionDefect dataSet
  ≡ vecNormSquared (value dataSet)
    + projectionDefect dataSet
      * (inverseWaveNormSquared dataSet
          * vecNormSquared (wave dataSet) - 1ℚ)
projectionExpansion dataSet =
  solve
    ( inverseWaveNormSquared dataSet
    ∷ vx (wave dataSet)
    ∷ vy (wave dataSet)
    ∷ vz (wave dataSet)
    ∷ vx (value dataSet)
    ∷ vy (value dataSet)
    ∷ vz (value dataSet)
    ∷ [])

projectionPythagoras :
  (dataSet : RationalLerayData) →
  vecNormSquared (lerayProject dataSet)
    + projectionDefect dataSet
  ≡ vecNormSquared (value dataSet)
projectionPythagoras dataSet =
  trans
    (projectionExpansion dataSet)
    collapsed
  where
  collapsed :
    vecNormSquared (value dataSet)
      + projectionDefect dataSet
        * (inverseWaveNormSquared dataSet
            * vecNormSquared (wave dataSet) - 1ℚ)
    ≡ vecNormSquared (value dataSet)
  collapsed rewrite inverseCalibration dataSet =
    solve
      ( vecNormSquared (value dataSet)
      ∷ projectionDefect dataSet
      ∷ [])

projectionDefectNonnegative :
  (dataSet : RationalLerayData) →
  0ℚ ≤ projectionDefect dataSet
projectionDefectNonnegative dataSet =
  let
    dotSquareNonnegative :
      0ℚ ≤ L2.square (vecDot (wave dataSet) (value dataSet))
    dotSquareNonnegative =
      L2.squareNonnegative (vecDot (wave dataSet) (value dataSet))

    instance
      inverseIsNonnegative =
        nonNegative (inverseNonnegative dataSet)
      dotSquareIsNonnegative =
        nonNegative dotSquareNonnegative
      defectIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (inverseWaveNormSquared dataSet)
          (L2.square (vecDot (wave dataSet) (value dataSet)))
  in
  ℚₚ.nonNegative⁻¹ (projectionDefect dataSet)

rationalLerayContractive :
  (dataSet : RationalLerayData) →
  vecNormSquared (lerayProject dataSet)
  ≤ vecNormSquared (value dataSet)
rationalLerayContractive dataSet =
  let
    addDefect :
      vecNormSquared (lerayProject dataSet)
      ≤ vecNormSquared (lerayProject dataSet)
          + projectionDefect dataSet
    addDefect =
      subst
        (λ lower →
          lower
          ≤ vecNormSquared (lerayProject dataSet)
            + projectionDefect dataSet)
        (ℚₚ.+-identityʳ (vecNormSquared (lerayProject dataSet)))
        (ℚₚ.+-mono-≤
          ℚₚ.≤-refl
          (projectionDefectNonnegative dataSet))
  in
  subst
    (λ upper → vecNormSquared (lerayProject dataSet) ≤ upper)
    (projectionPythagoras dataSet)
    addDefect

vectorPairs : Vec3 → Vec3 → List L2.Pair
vectorPairs left right =
  (vx left , vx right)
  ∷ (vy left , vy right)
  ∷ (vz left , vz right)
  ∷ []

pairDotMeaning :
  (left right : Vec3) →
  L2.pairDot (vectorPairs left right) ≡ vecDot left right
pairDotMeaning left right = solve []

leftNormMeaning :
  (left right : Vec3) →
  L2.leftNormSquared (vectorPairs left right)
  ≡ vecNormSquared left
leftNormMeaning left right = solve []

rightNormMeaning :
  (left right : Vec3) →
  L2.rightNormSquared (vectorPairs left right)
  ≡ vecNormSquared right
rightNormMeaning left right = solve []

vectorCauchySquared :
  (left right : Vec3) →
  L2.square (vecDot left right)
  ≤ vecNormSquared left * vecNormSquared right
vectorCauchySquared left right =
  subst
    (λ dotValue →
      L2.square dotValue
      ≤ vecNormSquared left * vecNormSquared right)
    (pairDotMeaning left right)
    (subst
      (λ leftNorm →
        L2.square (L2.pairDot (vectorPairs left right))
        ≤ leftNorm * vecNormSquared right)
      (leftNormMeaning left right)
      (subst
        (λ rightNorm →
          L2.square (L2.pairDot (vectorPairs left right))
          ≤ L2.leftNormSquared (vectorPairs left right) * rightNorm)
        (rightNormMeaning left right)
        (L2.finiteCauchySchwarzSquared (vectorPairs left right))))

record Matrix3 : Set where
  constructor matrix3
  field
    columnX columnY columnZ : Vec3

open Matrix3 public

matrixNormSquared : Matrix3 → ℚ
matrixNormSquared matrix =
  vecNormSquared (columnX matrix)
  + vecNormSquared (columnY matrix)
  + vecNormSquared (columnZ matrix)

divergenceVector : Vec3 → Matrix3 → Vec3
divergenceVector waveVector matrix =
  vec3
    (vecDot waveVector (columnX matrix))
    (vecDot waveVector (columnY matrix))
    (vecDot waveVector (columnZ matrix))

divergenceSquareBound :
  (waveVector : Vec3) →
  (matrix : Matrix3) →
  vecNormSquared (divergenceVector waveVector matrix)
  ≤ vecNormSquared waveVector * matrixNormSquared matrix
divergenceSquareBound waveVector matrix =
  let
    summed :
      L2.square (vecDot waveVector (columnX matrix))
        + L2.square (vecDot waveVector (columnY matrix))
        + L2.square (vecDot waveVector (columnZ matrix))
      ≤ vecNormSquared waveVector * vecNormSquared (columnX matrix)
        + vecNormSquared waveVector * vecNormSquared (columnY matrix)
        + vecNormSquared waveVector * vecNormSquared (columnZ matrix)
    summed =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (vectorCauchySquared waveVector (columnX matrix))
          (vectorCauchySquared waveVector (columnY matrix)))
        (vectorCauchySquared waveVector (columnZ matrix))

    targetMeaning :
      vecNormSquared waveVector * vecNormSquared (columnX matrix)
        + vecNormSquared waveVector * vecNormSquared (columnY matrix)
        + vecNormSquared waveVector * vecNormSquared (columnZ matrix)
      ≡ vecNormSquared waveVector * matrixNormSquared matrix
    targetMeaning =
      solve
        ( vecNormSquared waveVector
        ∷ vecNormSquared (columnX matrix)
        ∷ vecNormSquared (columnY matrix)
        ∷ vecNormSquared (columnZ matrix)
        ∷ [])
  in
  subst
    (λ upper →
      vecNormSquared (divergenceVector waveVector matrix) ≤ upper)
    targetMeaning
    summed

record ProjectedDivergenceData : Set where
  constructor projected-divergence-data
  field
    waveVector : Vec3
    tensor : Matrix3
    inverseWaveSquare : ℚ
    inverseWaveSquareNonnegative : 0ℚ ≤ inverseWaveSquare
    inverseWaveSquareCalibration :
      inverseWaveSquare * vecNormSquared waveVector ≡ 1ℚ

open ProjectedDivergenceData public

projectedDivergence : ProjectedDivergenceData → Vec3
projectedDivergence dataSet =
  lerayProject
    (rational-leray-data
      (waveVector dataSet)
      (divergenceVector (waveVector dataSet) (tensor dataSet))
      (inverseWaveSquare dataSet)
      (inverseWaveSquareNonnegative dataSet)
      (inverseWaveSquareCalibration dataSet))

projectedDivergenceSquareBound :
  (dataSet : ProjectedDivergenceData) →
  vecNormSquared (projectedDivergence dataSet)
  ≤ vecNormSquared (waveVector dataSet)
      * matrixNormSquared (tensor dataSet)
projectedDivergenceSquareBound dataSet =
  ℚₚ.≤-trans
    (rationalLerayContractive
      (rational-leray-data
        (waveVector dataSet)
        (divergenceVector (waveVector dataSet) (tensor dataSet))
        (inverseWaveSquare dataSet)
        (inverseWaveSquareNonnegative dataSet)
        (inverseWaveSquareCalibration dataSet)))
    (divergenceSquareBound (waveVector dataSet) (tensor dataSet))

record ComplexMatrix3 : Set where
  constructor complex-matrix3
  field
    realTensor imaginaryTensor : Matrix3

open ComplexMatrix3 public

complexMatrixNormSquared : ComplexMatrix3 → ℚ
complexMatrixNormSquared matrix =
  matrixNormSquared (realTensor matrix)
  + matrixNormSquared (imaginaryTensor matrix)

record ComplexProjectedDivergenceData : Set where
  constructor complex-projected-divergence-data
  field
    complexWaveVector : Vec3
    complexTensor : ComplexMatrix3
    complexInverseWaveSquare : ℚ
    complexInverseNonnegative : 0ℚ ≤ complexInverseWaveSquare
    complexInverseCalibration :
      complexInverseWaveSquare * vecNormSquared complexWaveVector ≡ 1ℚ

open ComplexProjectedDivergenceData public

realProjectedData : ComplexProjectedDivergenceData → ProjectedDivergenceData
realProjectedData dataSet =
  projected-divergence-data
    (complexWaveVector dataSet)
    (realTensor (complexTensor dataSet))
    (complexInverseWaveSquare dataSet)
    (complexInverseNonnegative dataSet)
    (complexInverseCalibration dataSet)

imaginaryProjectedData : ComplexProjectedDivergenceData → ProjectedDivergenceData
imaginaryProjectedData dataSet =
  projected-divergence-data
    (complexWaveVector dataSet)
    (imaginaryTensor (complexTensor dataSet))
    (complexInverseWaveSquare dataSet)
    (complexInverseNonnegative dataSet)
    (complexInverseCalibration dataSet)

complexProjectedSquare : ComplexProjectedDivergenceData → ℚ
complexProjectedSquare dataSet =
  vecNormSquared (projectedDivergence (realProjectedData dataSet))
  + vecNormSquared (projectedDivergence (imaginaryProjectedData dataSet))

complexProjectedDivergenceSquareBound :
  (dataSet : ComplexProjectedDivergenceData) →
  complexProjectedSquare dataSet
  ≤ vecNormSquared (complexWaveVector dataSet)
      * complexMatrixNormSquared (complexTensor dataSet)
complexProjectedDivergenceSquareBound dataSet =
  let
    summed :
      complexProjectedSquare dataSet
      ≤ vecNormSquared (complexWaveVector dataSet)
          * matrixNormSquared (realTensor (complexTensor dataSet))
        + vecNormSquared (complexWaveVector dataSet)
          * matrixNormSquared (imaginaryTensor (complexTensor dataSet))
    summed =
      ℚₚ.+-mono-≤
        (projectedDivergenceSquareBound (realProjectedData dataSet))
        (projectedDivergenceSquareBound (imaginaryProjectedData dataSet))

    targetMeaning :
      vecNormSquared (complexWaveVector dataSet)
          * matrixNormSquared (realTensor (complexTensor dataSet))
        + vecNormSquared (complexWaveVector dataSet)
          * matrixNormSquared (imaginaryTensor (complexTensor dataSet))
      ≡ vecNormSquared (complexWaveVector dataSet)
          * complexMatrixNormSquared (complexTensor dataSet)
    targetMeaning =
      solve
        ( vecNormSquared (complexWaveVector dataSet)
        ∷ matrixNormSquared (realTensor (complexTensor dataSet))
        ∷ matrixNormSquared (imaginaryTensor (complexTensor dataSet))
        ∷ [])
  in
  subst
    (λ upper → complexProjectedSquare dataSet ≤ upper)
    targetMeaning
    summed

complexHMinusOneSquared : ComplexProjectedDivergenceData → ℚ
complexHMinusOneSquared dataSet =
  complexInverseWaveSquare dataSet * complexProjectedSquare dataSet

complexHMinusOneCancellation :
  (dataSet : ComplexProjectedDivergenceData) →
  complexHMinusOneSquared dataSet
  ≤ complexMatrixNormSquared (complexTensor dataSet)
complexHMinusOneCancellation dataSet =
  let
    multiplied :
      complexInverseWaveSquare dataSet * complexProjectedSquare dataSet
      ≤ complexInverseWaveSquare dataSet
        * (vecNormSquared (complexWaveVector dataSet)
          * complexMatrixNormSquared (complexTensor dataSet))
    multiplied =
      let
        instance
          inverseIsNonnegative =
            nonNegative (complexInverseNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (complexInverseWaveSquare dataSet)
        (complexProjectedDivergenceSquareBound dataSet)

    associated :
      complexInverseWaveSquare dataSet
        * (vecNormSquared (complexWaveVector dataSet)
          * complexMatrixNormSquared (complexTensor dataSet))
      ≡ (complexInverseWaveSquare dataSet
          * vecNormSquared (complexWaveVector dataSet))
        * complexMatrixNormSquared (complexTensor dataSet)
    associated =
      solve
        ( complexInverseWaveSquare dataSet
        ∷ vecNormSquared (complexWaveVector dataSet)
        ∷ complexMatrixNormSquared (complexTensor dataSet)
        ∷ [])

    calibrated :
      (complexInverseWaveSquare dataSet
          * vecNormSquared (complexWaveVector dataSet))
        * complexMatrixNormSquared (complexTensor dataSet)
      ≡ complexMatrixNormSquared (complexTensor dataSet)
    calibrated rewrite complexInverseCalibration dataSet =
      solve (complexMatrixNormSquared (complexTensor dataSet) ∷ [])

    normalizedUpper :
      complexInverseWaveSquare dataSet
        * (vecNormSquared (complexWaveVector dataSet)
          * complexMatrixNormSquared (complexTensor dataSet))
      ≡ complexMatrixNormSquared (complexTensor dataSet)
    normalizedUpper = trans associated calibrated
  in
  subst
    (λ upper → complexHMinusOneSquared dataSet ≤ upper)
    normalizedUpper
    multiplied
