module DASHI.Physics.Closure.NSTriadKNLuoFilteredPairwiseDefectFiniteExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
--
-- DASHI CONTRIBUTION
--
-- A finite quadrature of Yu's pairwise filtered-direction defect is built from
-- literal nonnegative kernel cells.  The exact ordered-amplitude identity from
-- NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact proves cellwise
--
--   w min(a,b)^2 |xi-eta|^2
--     <= w |a xi-b eta|^2,
--
-- and recursive summation proves the finite pairwise defect is bounded by the
-- finite first-order vorticity-increment envelope with constant one.
--
-- The final two transport lemmas isolate exactly what remains analytic:
-- principal-value kernel contraction and the continuum difference-quotient to
-- filtered-diffusion estimate.  Neither is silently assumed to follow from
-- the finite sum.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact as Increment

record FilteredPairCell : Set where
  constructor filteredPairCell
  field
    kernelWeight : ℚ
    kernelWeightNonnegative : 0ℚ ≤ kernelWeight
    orderedIncrement : Increment.OrderedDirectionIncrement

open FilteredPairCell public

cellPairwiseDefect : FilteredPairCell → ℚ
cellPairwiseDefect cell =
  kernelWeight cell
  * Increment.weightedDirectionIncrement (orderedIncrement cell)

cellIncrementEnvelope : FilteredPairCell → ℚ
cellIncrementEnvelope cell =
  kernelWeight cell
  * Increment.vorticityIncrementSquared (orderedIncrement cell)

weightedDirectionNonnegative :
  ∀ dataSet →
  0ℚ ≤ Increment.weightedDirectionIncrement dataSet
weightedDirectionNonnegative dataSet =
  let
    amplitudeSquare =
      L2.square (Increment.smallerAmplitude dataSet)
    directionSquare =
      Increment.directionIncrementSquared dataSet

    instance
      amplitudeNN =
        nonNegative
          (L2.squareNonnegative
            (Increment.smallerAmplitude dataSet))
      directionNN =
        nonNegative
          (Gram.normSquaredNonnegative
            (Increment.vectorDifference
              (Increment.smallerDirection dataSet)
              (Increment.largerDirection dataSet)))
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg amplitudeSquare directionSquare
  in
  ℚₚ.nonNegative⁻¹
    (Increment.weightedDirectionIncrement dataSet)

cellPairwiseBelowIncrement :
  ∀ cell → cellPairwiseDefect cell ≤ cellIncrementEnvelope cell
cellPairwiseBelowIncrement cell =
  L2.nonnegativeProductMonotone
    (kernelWeightNonnegative cell)
    (weightedDirectionNonnegative (orderedIncrement cell))
    (kernelWeightNonnegative cell)
    (Gram.normSquaredNonnegative
      (Increment.vectorDifference
        (Increment.smallerVorticity (orderedIncrement cell))
        (Increment.largerVorticity (orderedIncrement cell))))
    ℚₚ.≤-refl
    (Increment.magnitudeWeightedDirectionIncrementBound
      (orderedIncrement cell))

finitePairwiseDefect : List FilteredPairCell → ℚ
finitePairwiseDefect [] = 0ℚ
finitePairwiseDefect (cell ∷ cells) =
  cellPairwiseDefect cell + finitePairwiseDefect cells

finiteIncrementEnvelope : List FilteredPairCell → ℚ
finiteIncrementEnvelope [] = 0ℚ
finiteIncrementEnvelope (cell ∷ cells) =
  cellIncrementEnvelope cell + finiteIncrementEnvelope cells

finitePairwiseDefectBelowIncrementEnvelope :
  ∀ cells →
  finitePairwiseDefect cells ≤ finiteIncrementEnvelope cells
finitePairwiseDefectBelowIncrementEnvelope [] = ℚₚ.≤-refl
finitePairwiseDefectBelowIncrementEnvelope (cell ∷ cells) =
  ℚₚ.+-mono-≤
    (cellPairwiseBelowIncrement cell)
    (finitePairwiseDefectBelowIncrementEnvelope cells)

record FiniteKernelContractionData : Set where
  constructor finiteKernelContractionData
  field
    cells : List FilteredPairCell
    nearFieldPositiveStretching contractionCoefficient : ℚ
    nearFieldNonnegative : 0ℚ ≤ nearFieldPositiveStretching
    contractionCoefficientNonnegative : 0ℚ ≤ contractionCoefficient
    contractionCoefficientAtMostOne : contractionCoefficient ≤ 1ℚ
    kernelContraction :
      nearFieldPositiveStretching
      ≤ contractionCoefficient * finitePairwiseDefect cells

open FiniteKernelContractionData public

finiteNearFieldBelowIncrementEnvelope :
  ∀ dataSet →
  nearFieldPositiveStretching dataSet
  ≤ finiteIncrementEnvelope (cells dataSet)
finiteNearFieldBelowIncrementEnvelope dataSet =
  let
    pairwise = finitePairwiseDefect (cells dataSet)

    pairwiseNonnegative : 0ℚ ≤ pairwise
    pairwiseNonnegative =
      let
        prove : ∀ cells → 0ℚ ≤ finitePairwiseDefect cells
        prove [] = ℚₚ.≤-refl
        prove (cell ∷ cells) =
          L2.addNonnegative
            productNonnegative
            (prove cells)
          where
          productNonnegative : 0ℚ ≤ cellPairwiseDefect cell
          productNonnegative =
            let
              instance
                weightNN = nonNegative (kernelWeightNonnegative cell)
                defectNN =
                  nonNegative
                    (weightedDirectionNonnegative
                      (orderedIncrement cell))
                productNN =
                  ℚₚ.nonNeg*nonNeg⇒nonNeg
                    (kernelWeight cell)
                    (Increment.weightedDirectionIncrement
                      (orderedIncrement cell))
            in
            ℚₚ.nonNegative⁻¹ (cellPairwiseDefect cell)
      in
      prove (cells dataSet)

    coefficientTimesPairwiseBelowPairwise :
      contractionCoefficient dataSet * pairwise ≤ pairwise
    coefficientTimesPairwiseBelowPairwise =
      let
        scaled =
          ℚₚ.*-monoʳ-≤-nonNeg
            pairwise
            (contractionCoefficientAtMostOne dataSet)

        rightClosed : 1ℚ * pairwise ≡ pairwise
        rightClosed = ℚₚ.*-identityˡ pairwise
      in
      subst
        (λ upper →
          contractionCoefficient dataSet * pairwise ≤ upper)
        rightClosed
        scaled
      where
      instance
        pairwiseNN = nonNegative pairwiseNonnegative
  in
  ℚₚ.≤-trans
    (kernelContraction dataSet)
    (ℚₚ.≤-trans
      coefficientTimesPairwiseBelowPairwise
      (finitePairwiseDefectBelowIncrementEnvelope
        (cells dataSet)))

record FiniteIncrementDiffusionBudget : Set where
  constructor finiteIncrementDiffusionBudget
  field
    contractionData : FiniteKernelContractionData
    eta diffusion lowerEnstrophyReservoir : ℚ
    etaNonnegative : 0ℚ ≤ eta
    diffusionNonnegative : 0ℚ ≤ diffusion
    reservoirNonnegative : 0ℚ ≤ lowerEnstrophyReservoir
    incrementToDiffusion :
      finiteIncrementEnvelope (cells contractionData)
      ≤ eta * diffusion + lowerEnstrophyReservoir

open FiniteIncrementDiffusionBudget public

finiteFilteredNearFieldCoercivity :
  ∀ budget →
  nearFieldPositiveStretching (contractionData budget)
  ≤ eta budget * diffusion budget
    + lowerEnstrophyReservoir budget
finiteFilteredNearFieldCoercivity budget =
  ℚₚ.≤-trans
    (finiteNearFieldBelowIncrementEnvelope
      (contractionData budget))
    (incrementToDiffusion budget)

record FilteredPairwiseAuthorityBoundary : Set where
  constructor filteredPairwiseAuthorityBoundary
  field
    finitePairwiseToIncrementProved : Set
    finiteKernelCoefficientTransportProved : Set
    continuumPrincipalValueLimitProved : Set
    continuumDifferenceQuotientCoercivityProved : Set

canonicalFilteredPairwiseAuthorityBoundary :
  FilteredPairwiseAuthorityBoundary
canonicalFilteredPairwiseAuthorityBoundary =
  filteredPairwiseAuthorityBoundary ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
