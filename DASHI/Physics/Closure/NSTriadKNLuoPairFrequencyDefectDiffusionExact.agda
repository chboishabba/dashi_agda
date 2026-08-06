module DASHI.Physics.Closure.NSTriadKNLuoPairFrequencyDefectDiffusionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D Navier-Stokes
-- and Euler Equations: The Use of Kolmogorov's Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
--
-- DASHI CONTRIBUTION
--
-- The physical-space product rule for |omega(x) cross omega(x-y)|^2 has a
-- sign-indefinite mixed-gradient term.  The correct shell damping is instead
-- obtained before the two input frequencies are multiplied together.
--
-- A pair-frequency cell carries two input Laplacian eigenvalues lambda_L and
-- lambda_R, a common shell floor kappa and a nonnegative defect amplitude A.
-- From
--
--   kappa <= lambda_L,     kappa <= lambda_R,
--
-- this module proves exactly
--
--   2 nu kappa A
--     <= nu (lambda_L + lambda_R) A.
--
-- The estimate is summed recursively over a finite Galerkin interaction list.
-- A separate zero-output witness records the high-high-to-low obstruction:
-- output-frequency Poincare damping can be zero while the two input
-- frequencies still contribute two units of diffusion.  Thus F3 must retain
-- pair-frequency information rather than projecting the defect product first.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record PairFrequencyDefectCell : Set where
  constructor pairFrequencyDefectCell
  field
    viscosity shellFloor leftEigenvalue rightEigenvalue defectAmplitude : ℚ

    viscosityNonnegative : 0ℚ ≤ viscosity
    shellFloorNonnegative : 0ℚ ≤ shellFloor
    leftEigenvalueNonnegative : 0ℚ ≤ leftEigenvalue
    rightEigenvalueNonnegative : 0ℚ ≤ rightEigenvalue
    defectAmplitudeNonnegative : 0ℚ ≤ defectAmplitude

    leftInShell : shellFloor ≤ leftEigenvalue
    rightInShell : shellFloor ≤ rightEigenvalue

open PairFrequencyDefectCell public

pairFrequencyDiffusion : PairFrequencyDefectCell → ℚ
pairFrequencyDiffusion cell =
  viscosity cell
  * (leftEigenvalue cell + rightEigenvalue cell)
  * defectAmplitude cell

shellDefectDamping : PairFrequencyDefectCell → ℚ
shellDefectDamping cell =
  2 * viscosity cell * shellFloor cell * defectAmplitude cell

twiceShellFloorBelowEigenvalueSum :
  ∀ cell →
  shellFloor cell + shellFloor cell
  ≤ leftEigenvalue cell + rightEigenvalue cell
twiceShellFloorBelowEigenvalueSum cell =
  ℚₚ.+-mono-≤ (leftInShell cell) (rightInShell cell)

pairFrequencyShellDamping :
  ∀ cell → shellDefectDamping cell ≤ pairFrequencyDiffusion cell
pairFrequencyShellDamping cell =
  let
    twoFloor = shellFloor cell + shellFloor cell
    eigenSum = leftEigenvalue cell + rightEigenvalue cell

    twoFloorNonnegative : 0ℚ ≤ twoFloor
    twoFloorNonnegative =
      L2.addNonnegative
        (shellFloorNonnegative cell)
        (shellFloorNonnegative cell)

    eigenSumNonnegative : 0ℚ ≤ eigenSum
    eigenSumNonnegative =
      L2.addNonnegative
        (leftEigenvalueNonnegative cell)
        (rightEigenvalueNonnegative cell)

    viscosityTimesFloor :
      viscosity cell * twoFloor
      ≤ viscosity cell * eigenSum
    viscosityTimesFloor =
      L2.nonnegativeProductMonotone
        (viscosityNonnegative cell)
        twoFloorNonnegative
        (viscosityNonnegative cell)
        eigenSumNonnegative
        ℚₚ.≤-refl
        (twiceShellFloorBelowEigenvalueSum cell)

    leftProductNonnegative :
      0ℚ ≤ viscosity cell * twoFloor
    leftProductNonnegative =
      let
        instance
          viscosityNN = nonNegative (viscosityNonnegative cell)
          floorNN = nonNegative twoFloorNonnegative
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg (viscosity cell) twoFloor
      in
      ℚₚ.nonNegative⁻¹ (viscosity cell * twoFloor)

    rightProductNonnegative :
      0ℚ ≤ viscosity cell * eigenSum
    rightProductNonnegative =
      let
        instance
          viscosityNN = nonNegative (viscosityNonnegative cell)
          eigenNN = nonNegative eigenSumNonnegative
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg (viscosity cell) eigenSum
      in
      ℚₚ.nonNegative⁻¹ (viscosity cell * eigenSum)

    withAmplitude :
      viscosity cell * twoFloor * defectAmplitude cell
      ≤ viscosity cell * eigenSum * defectAmplitude cell
    withAmplitude =
      L2.nonnegativeProductMonotone
        leftProductNonnegative
        (defectAmplitudeNonnegative cell)
        rightProductNonnegative
        (defectAmplitudeNonnegative cell)
        viscosityTimesFloor
        ℚₚ.≤-refl

    leftMeaning :
      viscosity cell * twoFloor * defectAmplitude cell
      ≡ shellDefectDamping cell
    leftMeaning =
      solve
        ( viscosity cell
        ∷ shellFloor cell
        ∷ defectAmplitude cell
        ∷ [])
  in
  subst
    (λ left → left ≤ pairFrequencyDiffusion cell)
    leftMeaning
    withAmplitude

sumPairFrequencyDiffusion : List PairFrequencyDefectCell → ℚ
sumPairFrequencyDiffusion [] = 0ℚ
sumPairFrequencyDiffusion (cell ∷ cells) =
  pairFrequencyDiffusion cell + sumPairFrequencyDiffusion cells

sumShellDefectDamping : List PairFrequencyDefectCell → ℚ
sumShellDefectDamping [] = 0ℚ
sumShellDefectDamping (cell ∷ cells) =
  shellDefectDamping cell + sumShellDefectDamping cells

finitePairFrequencyShellDamping :
  ∀ cells →
  sumShellDefectDamping cells ≤ sumPairFrequencyDiffusion cells
finitePairFrequencyShellDamping [] = ℚₚ.≤-refl
finitePairFrequencyShellDamping (cell ∷ cells) =
  ℚₚ.+-mono-≤
    (pairFrequencyShellDamping cell)
    (finitePairFrequencyShellDamping cells)

zeroOutputFrequencyDamping : ℚ
zeroOutputFrequencyDamping = 1ℚ * 0ℚ * 1ℚ

unitInputPairDiffusion : ℚ
unitInputPairDiffusion = 1ℚ * (1ℚ + 1ℚ) * 1ℚ

zeroOutputDampingCloses : zeroOutputFrequencyDamping ≡ 0ℚ
zeroOutputDampingCloses = solve []

unitInputPairDiffusionCloses : unitInputPairDiffusion ≡ 2
unitInputPairDiffusionCloses = solve []

highHighLowOutputMissesTwoUnits :
  zeroOutputFrequencyDamping + 2 ≡ unitInputPairDiffusion
highHighLowOutputMissesTwoUnits = solve []

record PairFrequencyDiffusionAuthorityBoundary : Set where
  constructor pairFrequencyDiffusionAuthorityBoundary
  field
    cellwiseInputFrequencyDampingProved : Set
    finiteGalerkinPairSummationProved : Set
    highHighLowOutputObstructionExposed : Set
    actualFourierPairExpansionConstructed : Set
    annularKernelWeightsMatched : Set
    cutoffUniformPhysicalDampingProduced : Set

canonicalPairFrequencyDiffusionAuthorityBoundary :
  PairFrequencyDiffusionAuthorityBoundary
canonicalPairFrequencyDiffusionAuthorityBoundary =
  pairFrequencyDiffusionAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
