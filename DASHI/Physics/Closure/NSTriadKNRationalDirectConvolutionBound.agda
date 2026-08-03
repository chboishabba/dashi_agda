module DASHI.Physics.Closure.NSTriadKNRationalDirectConvolutionBound where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz; Hajer Bahouri;
-- Jean-Yves Chemin; Raphael Danchin; Loukas Grafakos; Seungly Oh; DASHI
-- repository contributors.
-- Title: "Finite low-output direct-convolution inequality for the first
-- Navier--Stokes partial adjoint".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; Communications in Partial Differential Equations 39
-- (2014), 1128--1157; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7;
-- 10.1080/03605302.2013.822885; the discrete finite-fibre theorem is
-- repository-original and has no DOI.
-- Uses: the exact rational finite squared Cauchy--Schwarz theorem, one
-- restricted resonant pair list per output, and a multiplier-square bound.
-- Relationship: proves the algebraic core of the single hard direct T*1
-- component. Shell cardinality, the literal projected multiplier, Sobolev
-- weights and the constructive-real geometric series remain separate
-- adapters rather than hidden hypotheses.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

fibreValue : ℚ → List L2.Pair → ℚ
fibreValue multiplier pairs = multiplier * L2.pairDot pairs

fibreValueSquared : ℚ → List L2.Pair → ℚ
fibreValueSquared multiplier pairs = L2.square (fibreValue multiplier pairs)

multiplierTimesCauchySchwarz :
  ∀ multiplier pairs →
  fibreValueSquared multiplier pairs
  ≤ L2.square multiplier
    * (L2.leftNormSquared pairs * L2.rightNormSquared pairs)
multiplierTimesCauchySchwarz multiplier pairs =
  let
    instance multiplierSquaredNN =
      nonNegative (L2.squareNonnegative multiplier)
    multiplied = ℚₚ.*-monoˡ-≤-nonNeg
      (L2.square multiplier)
      (L2.finiteCauchySchwarzSquared pairs)
  in
  subst
    (λ left → left ≤
      L2.square multiplier
      * (L2.leftNormSquared pairs * L2.rightNormSquared pairs))
    (solve (multiplier ∷ L2.pairDot pairs ∷ []))
    multiplied

record FibreMajorant
    (fullLeftNorm fullRightNorm multiplierBoundSquared : ℚ)
    (multiplier : ℚ)
    (pairs : List L2.Pair) : Set where
  field
    leftRestriction : L2.leftNormSquared pairs ≤ fullLeftNorm
    rightRestriction : L2.rightNormSquared pairs ≤ fullRightNorm
    fullLeftNonnegative : 0ℚ ≤ fullLeftNorm
    fullRightNonnegative : 0ℚ ≤ fullRightNorm
    multiplierBoundNonnegative : 0ℚ ≤ multiplierBoundSquared
    multiplierSquaredBound : L2.square multiplier ≤ multiplierBoundSquared

open FibreMajorant public

fibreMajorantSquared :
  ∀ {fullLeftNorm fullRightNorm multiplierBoundSquared multiplier pairs} →
  FibreMajorant fullLeftNorm fullRightNorm multiplierBoundSquared multiplier pairs →
  fibreValueSquared multiplier pairs
  ≤ multiplierBoundSquared * (fullLeftNorm * fullRightNorm)
fibreMajorantSquared
  {fullLeftNorm} {fullRightNorm} {multiplierBoundSquared} {multiplier} {pairs}
  majorant =
  let
    restrictedProduct = L2.nonnegativeProductMonotone
      (L2.leftNormSquaredNonnegative pairs)
      (L2.rightNormSquaredNonnegative pairs)
      (fullLeftNonnegative majorant)
      (fullRightNonnegative majorant)
      (leftRestriction majorant)
      (rightRestriction majorant)

    cauchy = multiplierTimesCauchySchwarz multiplier pairs

    pairProductNonnegative :
      0ℚ ≤ L2.leftNormSquared pairs * L2.rightNormSquared pairs
    pairProductNonnegative =
      let
        instance
          leftNN = nonNegative (L2.leftNormSquaredNonnegative pairs)
          rightNN = nonNegative (L2.rightNormSquaredNonnegative pairs)
          productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg
            (L2.leftNormSquared pairs) (L2.rightNormSquared pairs)
      in ℚₚ.nonNegative⁻¹
        (L2.leftNormSquared pairs * L2.rightNormSquared pairs)

    multiplierStage :
      L2.square multiplier
        * (L2.leftNormSquared pairs * L2.rightNormSquared pairs)
      ≤ multiplierBoundSquared
        * (L2.leftNormSquared pairs * L2.rightNormSquared pairs)
    multiplierStage =
      let instance pairProductNN = nonNegative pairProductNonnegative
      in ℚₚ.*-monoʳ-≤-nonNeg
        (L2.leftNormSquared pairs * L2.rightNormSquared pairs)
        (multiplierSquaredBound majorant)

    fullStage :
      multiplierBoundSquared
        * (L2.leftNormSquared pairs * L2.rightNormSquared pairs)
      ≤ multiplierBoundSquared * (fullLeftNorm * fullRightNorm)
    fullStage =
      let instance multiplierNN =
        nonNegative (multiplierBoundNonnegative majorant)
      in ℚₚ.*-monoˡ-≤-nonNeg multiplierBoundSquared restrictedProduct
  in
  ℚₚ.≤-trans cauchy (ℚₚ.≤-trans multiplierStage fullStage)

record OutputFibre
    (fullLeftNorm fullRightNorm multiplierBoundSquared : ℚ) : Set where
  constructor output-fibre
  field
    multiplier : ℚ
    pairs : List L2.Pair
    majorant : FibreMajorant
      fullLeftNorm fullRightNorm multiplierBoundSquared multiplier pairs

open OutputFibre public

outputFibreSquared :
  ∀ {fullLeftNorm fullRightNorm multiplierBoundSquared} →
  OutputFibre fullLeftNorm fullRightNorm multiplierBoundSquared → ℚ
outputFibreSquared fibre = fibreValueSquared (multiplier fibre) (pairs fibre)

sumOutputFibreSquares :
  ∀ {fullLeftNorm fullRightNorm multiplierBoundSquared} →
  List (OutputFibre fullLeftNorm fullRightNorm multiplierBoundSquared) → ℚ
sumOutputFibreSquares [] = 0ℚ
sumOutputFibreSquares (fibre ∷ rest) =
  outputFibreSquared fibre + sumOutputFibreSquares rest

repeatOutputBound :
  ∀ {fullLeftNorm fullRightNorm multiplierBoundSquared} →
  List (OutputFibre fullLeftNorm fullRightNorm multiplierBoundSquared) → ℚ
repeatOutputBound {fullLeftNorm} {fullRightNorm} {multiplierBoundSquared} [] = 0ℚ
repeatOutputBound {fullLeftNorm} {fullRightNorm} {multiplierBoundSquared}
  (_ ∷ rest) =
  multiplierBoundSquared * (fullLeftNorm * fullRightNorm)
  + repeatOutputBound rest

finiteLowOutputConvolutionBoundSquared :
  ∀ {fullLeftNorm fullRightNorm multiplierBoundSquared}
    (outputs : List
      (OutputFibre fullLeftNorm fullRightNorm multiplierBoundSquared)) →
  sumOutputFibreSquares outputs ≤ repeatOutputBound outputs
finiteLowOutputConvolutionBoundSquared [] = ℚₚ.≤-refl
finiteLowOutputConvolutionBoundSquared (fibre ∷ rest) =
  ℚₚ.+-mono-≤
    (fibreMajorantSquared (majorant fibre))
    (finiteLowOutputConvolutionBoundSquared rest)

record ShellCardinalityMajorant
    {fullLeftNorm fullRightNorm multiplierBoundSquared : ℚ}
    (outputs : List
      (OutputFibre fullLeftNorm fullRightNorm multiplierBoundSquared)) : Set where
  field
    shellCardinalityFactor : ℚ
    shellCardinalityFactorNonnegative : 0ℚ ≤ shellCardinalityFactor
    repeatedBoundCollapses :
      repeatOutputBound outputs
      ≡ shellCardinalityFactor
        * (multiplierBoundSquared * (fullLeftNorm * fullRightNorm))

open ShellCardinalityMajorant public

finiteLowOutputShellBoundSquared :
  ∀ {fullLeftNorm fullRightNorm multiplierBoundSquared outputs} →
  (cardinality : ShellCardinalityMajorant
    {fullLeftNorm} {fullRightNorm} {multiplierBoundSquared} outputs) →
  sumOutputFibreSquares outputs
  ≤ shellCardinalityFactor cardinality
      * (multiplierBoundSquared * (fullLeftNorm * fullRightNorm))
finiteLowOutputShellBoundSquared {outputs = outputs} cardinality =
  subst
    (λ upper → sumOutputFibreSquares outputs ≤ upper)
    (repeatedBoundCollapses cardinality)
    (finiteLowOutputConvolutionBoundSquared outputs)

finiteDirectConvolutionAlgebraClosed : Bool
finiteDirectConvolutionAlgebraClosed = true

finiteDirectConvolutionAlgebraClosedIsTrue :
  finiteDirectConvolutionAlgebraClosed ≡ true
finiteDirectConvolutionAlgebraClosedIsTrue = refl

cutoffUniformSobolevSummationStillRequired : Bool
cutoffUniformSobolevSummationStillRequired = true

cutoffUniformSobolevSummationStillRequiredIsTrue :
  cutoffUniformSobolevSummationStillRequired ≡ true
cutoffUniformSobolevSummationStillRequiredIsTrue = refl
