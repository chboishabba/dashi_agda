{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact where

------------------------------------------------------------------------
-- A3 / CENTERED QUADRATIC-KERNEL NORMAL FORM
--
-- Combine:
--
--   R490-era centered A3 identity
--
--     S_A3
--       = n * (- sum r_tau W(M,A_tau))
--         + (sum r_tau) W(M,M),
--
-- with the complete-fibre kernel collapses
--
--     K   = sum iK_tau     = 4 M,
--     K_r = sum r_tau iK_tau = 4 sum r_tau A_tau.
--
-- Therefore, division-free,
--
--   4 S_A3
--     = n * (- W(M,K_r))
--       + (sum r_tau) W(M,K).
--
-- This is exact finite algebra.  It replaces the O(n^2) pair-difference target
-- by one centered quadratic-kernel aggregate on the complete physical fibre.
-- No pointwise R205 identification, lower separation, Pluecker estimate,
-- absolute value or analytic inequality is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Vector
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNA3CenteredVectorWorkNormalFormExact as Centered
import DASHI.Physics.Closure.NSTriadKNRateWeightedMixedHelicityKernelCollapseExact as RateKernel

F : C3.RealField _
F = Rational.rationalRealField

four : ℚ
four = (1ℚ + 1ℚ) + (1ℚ + 1ℚ)

------------------------------------------------------------------------
-- Work against four copies.
------------------------------------------------------------------------

workFourCopies :
  (mixed value : C3.Complex3 F) →
  Work.coherentWork mixed (R225.fourCopies value)
  ≡ four * Work.coherentWork mixed value
workFourCopies mixed value =
  trans
    (Work.workAddRight mixed
      (C3.complex3Add value value)
      (C3.complex3Add value value))
    (trans
      (cong₂ _+_
        (Work.workAddRight mixed value value)
        (Work.workAddRight mixed value value))
      (solve (Work.coherentWork mixed value ∷ [])))

------------------------------------------------------------------------
-- Physical rate-weighted mixed cell is literally real scaling by cellRate.
------------------------------------------------------------------------

physicalRateWeightedMixedCellIsRealScale :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  RateKernel.weightedPlusMinus
    (RateKernel.physicalRateWeight rho) S velocity tau
  ≡
  R291.realScale (Pair.cellRate rho tau)
    (D1a.mixedProductCell S velocity tau)
physicalRateWeightedMixedCellIsRealScale rho S velocity tau = refl

------------------------------------------------------------------------
-- Convert weighted scalar work sum into work against weighted vector fold.
------------------------------------------------------------------------

weightedWorkSumIsWorkSumOfRateWeightedMixed :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (mixed : C3.Complex3 F) →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Pair.weightedWorkSum
    (Pair.cellRate rho)
    (Pair.cellWork mixed (D1a.mixedProductCell S velocity))
    items
  ≡
  Pair.workSum
    (Pair.cellWork mixed
      (RateKernel.weightedPlusMinus
        (RateKernel.physicalRateWeight rho) S velocity))
    items
weightedWorkSumIsWorkSumOfRateWeightedMixed
    mixed rho S velocity [] = refl
weightedWorkSumIsWorkSumOfRateWeightedMixed
    mixed rho S velocity (tau ∷ rest)
  rewrite weightedWorkSumIsWorkSumOfRateWeightedMixed
            mixed rho S velocity rest
        | physicalRateWeightedMixedCellIsRealScale rho S velocity tau
        | Work.workScaleRight
            (Pair.cellRate rho tau)
            mixed
            (D1a.mixedProductCell S velocity tau) = refl

weightedWorkSumAgainstRateWeightedFold :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (mixed : C3.Complex3 F) →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Pair.weightedWorkSum
    (Pair.cellRate rho)
    (Pair.cellWork mixed (D1a.mixedProductCell S velocity))
    items
  ≡
  Work.coherentWork mixed
    (R224.foldVector
      (RateKernel.weightedPlusMinus
        (RateKernel.physicalRateWeight rho) S velocity)
      items)
weightedWorkSumAgainstRateWeightedFold mixed rho S velocity items =
  trans
    (weightedWorkSumIsWorkSumOfRateWeightedMixed
      mixed rho S velocity items)
    (Pair.workSumAgainstFold
      mixed
      (RateKernel.weightedPlusMinus
        (RateKernel.physicalRateWeight rho) S velocity)
      items)

------------------------------------------------------------------------
-- Kernel work identities.
------------------------------------------------------------------------

rateWeightedKernelWorkIsFourWeightedWork :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    {velocity : Z3.FourierMode → C3.Complex3 F} →
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity) →
  (rho : Z3.FourierMode → ℚ) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    mixed = R224.foldVector (D1a.mixedProductCell S velocity) items
    weightedMixed =
      R224.foldVector
        (RateKernel.weightedPlusMinus
          (RateKernel.physicalRateWeight rho) S velocity)
        items
    weightedKernel =
      R224.foldVector
        (RateKernel.weightedIQuadraticKernel
          (RateKernel.physicalRateWeight rho) S velocity)
        items
  in
  Work.coherentWork mixed weightedKernel
  ≡
  four * Work.coherentWork mixed weightedMixed
rateWeightedKernelWorkIsFourWeightedWork
    {S = S} {velocity = velocity} P rho cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    mixed = R224.foldVector (D1a.mixedProductCell S velocity) items
    weightedMixed =
      R224.foldVector
        (RateKernel.weightedPlusMinus
          (RateKernel.physicalRateWeight rho) S velocity)
        items
    weightedKernel =
      R224.foldVector
        (RateKernel.weightedIQuadraticKernel
          (RateKernel.physicalRateWeight rho) S velocity)
        items
    collapse :
      weightedKernel ≡ R225.fourCopies weightedMixed
    collapse =
      RateKernel.physicalRateWeightedQuadraticKernelCollapse
        P rho cutoff output
  in
  trans
    (cong (Work.coherentWork mixed) collapse)
    (workFourCopies mixed weightedMixed)

kernelWorkIsFourSelfWork :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    {velocity : Z3.FourierMode → C3.Complex3 F} →
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    mixed = R224.foldVector (D1a.mixedProductCell S velocity) items
    kernel =
      R224.foldVector (R225.iQuadraticKernelCell S velocity) items
  in
  Work.coherentWork mixed kernel
  ≡ four * Work.coherentWork mixed mixed
kernelWorkIsFourSelfWork {S = S} {velocity = velocity}
    P cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    mixed = R224.foldVector (D1a.mixedProductCell S velocity) items
    kernel = R224.foldVector (R225.iQuadraticKernelCell S velocity) items
    collapse : kernel ≡ R225.fourCopies mixed
    collapse =
      R225.fixedOutputQuadraticKernelIsFourMixedHelicityConvolution
        P cutoff output
  in
  trans
    (cong (Work.coherentWork mixed) collapse)
    (workFourCopies mixed mixed)

------------------------------------------------------------------------
-- Main division-free centered kernel normal form.
------------------------------------------------------------------------

fixedOutputSignedA3KernelCenteredNormalForm :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    {velocity : Z3.FourierMode → C3.Complex3 F} →
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity) →
  (rho : Z3.FourierMode → ℚ) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = Pair.cellRate rho
    weightedKernel =
      R224.foldVector
        (RateKernel.weightedIQuadraticKernel
          (RateKernel.physicalRateWeight rho) S velocity)
        items
    kernel =
      R224.foldVector (R225.iQuadraticKernelCell S velocity) items
    signedA3 =
      0ℚ - Vector.pairDifferenceVectorWorkSum rate mixed value items
    n = Pair.natAsRational (length items)
    rateTotal = Pair.rateSum rate items
  in
  four * signedA3
  ≡
  n * (0ℚ - Work.coherentWork mixed weightedKernel)
    + rateTotal * Work.coherentWork mixed kernel
fixedOutputSignedA3KernelCenteredNormalForm
    {S = S} {velocity = velocity} P rho cutoff output
  rewrite
    Centered.fixedOutputSignedA3CenteredNormalForm
      rho S velocity cutoff output
        | weightedWorkSumAgainstRateWeightedFold
            (R224.foldVector
              (D1a.mixedProductCell S velocity)
              (Output.physicalOutputFiber cutoff output))
            rho S velocity
            (Output.physicalOutputFiber cutoff output)
        | rateWeightedKernelWorkIsFourWeightedWork
            P rho cutoff output
        | kernelWorkIsFourSelfWork P cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    mixed = R224.foldVector (D1a.mixedProductCell S velocity) items
    weightedMixed =
      R224.foldVector
        (RateKernel.weightedPlusMinus
          (RateKernel.physicalRateWeight rho) S velocity)
        items
    n = Pair.natAsRational (length items)
    rateTotal = Pair.rateSum (Pair.cellRate rho) items
    weightedWork = Work.coherentWork mixed weightedMixed
    selfWork = Work.coherentWork mixed mixed
  in
  solve (n ∷ rateTotal ∷ weightedWork ∷ selfWork ∷ [])

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

a3KernelCenteredNormalFormClosed : Bool
a3KernelCenteredNormalFormClosed = true

a3KernelCenteredNormalFormUsesPointwiseR205 : Bool
a3KernelCenteredNormalFormUsesPointwiseR205 = false

a3KernelCenteredNormalFormUsesLowerSeparation : Bool
a3KernelCenteredNormalFormUsesLowerSeparation = false

a3KernelCenteredNormalFormIntroducesEstimate : Bool
a3KernelCenteredNormalFormIntroducesEstimate = false

a3KernelCenteredNormalFormClosedIsTrue :
  a3KernelCenteredNormalFormClosed ≡ true
a3KernelCenteredNormalFormClosedIsTrue = refl

a3KernelCenteredNormalFormUsesPointwiseR205IsFalse :
  a3KernelCenteredNormalFormUsesPointwiseR205 ≡ false
a3KernelCenteredNormalFormUsesPointwiseR205IsFalse = refl

a3KernelCenteredNormalFormUsesLowerSeparationIsFalse :
  a3KernelCenteredNormalFormUsesLowerSeparation ≡ false
a3KernelCenteredNormalFormUsesLowerSeparationIsFalse = refl

a3KernelCenteredNormalFormIntroducesEstimateIsFalse :
  a3KernelCenteredNormalFormIntroducesEstimate ≡ false
a3KernelCenteredNormalFormIntroducesEstimateIsFalse = refl
