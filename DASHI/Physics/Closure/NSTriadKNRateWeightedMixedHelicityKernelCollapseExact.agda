{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNRateWeightedMixedHelicityKernelCollapseExact where

------------------------------------------------------------------------
-- RATE-WEIGHTED R225 / COMPLETE-FIBRE QUADRATIC KERNEL COLLAPSE
--
-- R225 proves, unweighted,
--
--   sum iK_tau = 4 sum A_tau,
--   A_tau = u^+_p x u^-_q.
--
-- R294 proves that arbitrary p/q-swap-invariant scalar weights preserve the
-- signed complete-fibre reindexing mechanism, and R295 proves the physical
-- damping rate
--
--   r_tau = rho(p_tau) + rho(q_tau)
--
-- is swap invariant.
--
-- This module combines those exact finite facts to prove
--
--   sum r_tau iK_tau = 4 sum r_tau A_tau
--
-- on the actual complete fixed-output fibre.  No norm or estimate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295

weightedPlusMinus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedPlusMinus W S velocity =
  R294.weightedCell W (R224.mixedPlusMinus S velocity)

weightedMinusPlus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedMinusPlus W S velocity =
  R294.weightedCell W (R224.mixedMinusPlus S velocity)

weightedMixedDifference :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedMixedDifference W S velocity tau =
  C3.complex3Subtract
    (weightedPlusMinus W S velocity tau)
    (weightedMinusPlus W S velocity tau)

weightedDoubleMixed :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedDoubleMixed W S velocity tau =
  C3.complex3Add
    (weightedMixedDifference W S velocity tau)
    (weightedMixedDifference W S velocity tau)

weightedIQuadraticKernel :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
weightedIQuadraticKernel W S velocity =
  R294.weightedCell W (R225.iQuadraticKernelCell S velocity)

weightedMinusPlusAfterSwapIsNegativePlusMinus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  weightedMinusPlus W S velocity (Symmetry.swapTriad tau)
  ≡ C3.complex3Negate (weightedPlusMinus W S velocity tau)
weightedMinusPlusAfterSwapIsNegativePlusMinus W S velocity tau =
  trans
    (cong
      (λ selectedWeight →
        C3.complex3Scale selectedWeight
          (R224.mixedMinusPlus S velocity (Symmetry.swapTriad tau)))
      (R294.swapInvariant W tau))
    (trans
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (R224.mixedMinusPlusAfterSwapIsNegativePlusMinus
          S velocity tau))
      (R73.complex3ScaleNegate
        (R294.weight W tau)
        (R224.mixedPlusMinus S velocity tau)))

weightedMinusPlusSumIsNegativePlusMinusSum :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (weightedMinusPlus W S velocity)
    (Output.physicalOutputFiber cutoff output)
  ≡ C3.complex3Negate
      (R224.foldVector (weightedPlusMinus W S velocity)
        (Output.physicalOutputFiber cutoff output))
weightedMinusPlusSumIsNegativePlusMinusSum W S velocity cutoff output =
  trans
    (sym
      (R224.foldPermutationInvariant
        (weightedMinusPlus W S velocity)
        (R224.swapOutputFibrePermutation cutoff output)))
    (trans
      (R224.foldMap
        (weightedMinusPlus W S velocity)
        Symmetry.swapTriad
        (Output.physicalOutputFiber cutoff output))
      (trans
        (pointwise (Output.physicalOutputFiber cutoff output))
        (R225.foldPointwiseNegate
          (weightedPlusMinus W S velocity)
          (Output.physicalOutputFiber cutoff output))))
  where
  pointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector
      (λ tau →
        weightedMinusPlus W S velocity (Symmetry.swapTriad tau))
      items
    ≡
    R224.foldVector
      (λ tau →
        C3.complex3Negate (weightedPlusMinus W S velocity tau))
      items
  pointwise [] = refl
  pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (weightedMinusPlusAfterSwapIsNegativePlusMinus
        W S velocity tau)
      (pointwise rest)

weightedDoubleMixedIsScaledDoubleMixed :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complex3Scale (R294.weight W tau)
    (R225.doubleMixedCell S velocity tau)
  ≡ weightedDoubleMixed W S velocity tau
weightedDoubleMixedIsScaledDoubleMixed W S velocity tau =
  trans
    (R73.complex3ScaleAdd
      (R294.weight W tau)
      (R225.mixedDifferenceCell S velocity tau)
      (R225.mixedDifferenceCell S velocity tau))
    (cong₂ C3.complex3Add
      (R73.complex3ScaleSubtract
        (R294.weight W tau)
        (R224.mixedPlusMinus S velocity tau)
        (R224.mixedMinusPlus S velocity tau))
      (R73.complex3ScaleSubtract
        (R294.weight W tau)
        (R224.mixedPlusMinus S velocity tau)
        (R224.mixedMinusPlus S velocity tau)))

weightedIQuadraticKernelIsWeightedDoubleMixed :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact.HelicalHalfCalibration S}
    {velocity : Z3.FourierMode → C3.Complex3 F}
    (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity)
    (W : R294.SwapInvariantCellWeight F)
    (tau : Physical.PhysicalTriadIncidence) →
  weightedIQuadraticKernel W S velocity tau
  ≡ weightedDoubleMixed W S velocity tau
weightedIQuadraticKernelIsWeightedDoubleMixed
    {S = S} {velocity = velocity} P W tau =
  trans
    (cong
      (C3.complex3Scale (R294.weight W tau))
      (R225.iQuadraticKernelCellIsDoubleMixedCell P tau))
    (weightedDoubleMixedIsScaledDoubleMixed W S velocity tau)

weightedDoubleMixedSumIsFourWeightedPlusMinus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (weightedDoubleMixed W S velocity)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R225.fourCopies
    (R224.foldVector (weightedPlusMinus W S velocity)
      (Output.physicalOutputFiber cutoff output))
weightedDoubleMixedSumIsFourWeightedPlusMinus {F = F}
    W S velocity cutoff output =
  let
    fibre = Output.physicalOutputFiber cutoff output
    A = R224.foldVector (weightedPlusMinus W S velocity) fibre
    B = R224.foldVector (weightedMinusPlus W S velocity) fibre
    Bneg = weightedMinusPlusSumIsNegativePlusMinusSum
      W S velocity cutoff output
    first = R225.foldPointwiseAdd
      (weightedMixedDifference W S velocity)
      (weightedMixedDifference W S velocity)
      fibre
    diff = R225.foldPointwiseSubtract
      (weightedPlusMinus W S velocity)
      (weightedMinusPlus W S velocity)
      fibre
    endpoint :
      C3.complex3Add
        (C3.complex3Subtract A (C3.complex3Negate A))
        (C3.complex3Subtract A (C3.complex3Negate A))
      ≡ R225.fourCopies A
    endpoint =
      R225.fixedOutputDoubleMixedSumIsFourPlusMinusSum
        S velocity cutoff output
      |> λ _ → additiveFour A
  in
  trans first
    (trans
      (cong₂ C3.complex3Add diff diff)
      (trans
        (cong₂ C3.complex3Add
          (cong (C3.complex3Subtract A) Bneg)
          (cong (C3.complex3Subtract A) Bneg))
        endpoint))
  where
  _|>_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  x |> f = f x

  additiveFour :
    (a : C3.Complex3 F) →
    C3.complex3Add
      (C3.complex3Subtract a (C3.complex3Negate a))
      (C3.complex3Subtract a (C3.complex3Negate a))
    ≡ R225.fourCopies a
  additiveFour (C3.complex3 ax ay az) =
    DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra.complex3Ext
      (R.solve 1 goal refl ax)
      (R.solve 1 goal refl ay)
      (R.solve 1 goal refl az)
    where
    module R =
      DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver F
    goal = λ x →
      ((x R.⊕ (R.⊝ (R.⊝ x))) R.⊕ (x R.⊕ (R.⊝ (R.⊝ x))))
      R.⊜ ((x R.⊕ x) R.⊕ (x R.⊕ x))

fixedOutputWeightedQuadraticKernelCollapse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact.HelicalHalfCalibration S}
    {velocity : Z3.FourierMode → C3.Complex3 F}
    (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity)
    (W : R294.SwapInvariantCellWeight F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (weightedIQuadraticKernel W S velocity)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R225.fourCopies
    (R224.foldVector (weightedPlusMinus W S velocity)
      (Output.physicalOutputFiber cutoff output))
fixedOutputWeightedQuadraticKernelCollapse
    {S = S} {velocity = velocity} P W cutoff output =
  trans
    (pointwise (Output.physicalOutputFiber cutoff output))
    (weightedDoubleMixedSumIsFourWeightedPlusMinus
      W S velocity cutoff output)
  where
  pointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector (weightedIQuadraticKernel W S velocity) items
    ≡ R224.foldVector (weightedDoubleMixed W S velocity) items
  pointwise [] = refl
  pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (weightedIQuadraticKernelIsWeightedDoubleMixed P W tau)
      (pointwise rest)

------------------------------------------------------------------------
-- Physical damping-rate specialization.
------------------------------------------------------------------------

physicalRateWeight :
  (rho : Z3.FourierMode → Data.Rational.Base.ℚ) →
  R294.SwapInvariantCellWeight R295.F
physicalRateWeight rho =
  R295.rateFunctionBuildsR294Weight rho (C3.realEmbed R295.F)

physicalRateWeightedQuadraticKernelCollapse :
  {E : C3.IntegerEmbedding R295.F}
  {I : C3.ModeInverseSquare R295.F E}
  {S : Helical.HelicalModeScalars R295.F}
  {L : Helical.PeriodicHelicalProjectorLaws R295.F E I S}
  {H : DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact.HelicalHalfCalibration S}
  {velocity : Z3.FourierMode → C3.Complex3 R295.F} →
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity) →
  (rho : Z3.FourierMode → Data.Rational.Base.ℚ) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector
    (weightedIQuadraticKernel (physicalRateWeight rho) S velocity)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R225.fourCopies
    (R224.foldVector
      (weightedPlusMinus (physicalRateWeight rho) S velocity)
      (Output.physicalOutputFiber cutoff output))
physicalRateWeightedQuadraticKernelCollapse P rho =
  fixedOutputWeightedQuadraticKernelCollapse P (physicalRateWeight rho)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

swapInvariantWeightedR225CollapseClosed : Bool
swapInvariantWeightedR225CollapseClosed = true

physicalRateWeightedR225CollapseClosed : Bool
physicalRateWeightedR225CollapseClosed = true

physicalRateWeightedR225CollapseUsesPointwiseSeparation : Bool
physicalRateWeightedR225CollapseUsesPointwiseSeparation = false

physicalRateWeightedR225CollapseIntroducesEstimate : Bool
physicalRateWeightedR225CollapseIntroducesEstimate = false

swapInvariantWeightedR225CollapseClosedIsTrue :
  swapInvariantWeightedR225CollapseClosed ≡ true
swapInvariantWeightedR225CollapseClosedIsTrue = refl

physicalRateWeightedR225CollapseClosedIsTrue :
  physicalRateWeightedR225CollapseClosed ≡ true
physicalRateWeightedR225CollapseClosedIsTrue = refl

physicalRateWeightedR225CollapseUsesPointwiseSeparationIsFalse :
  physicalRateWeightedR225CollapseUsesPointwiseSeparation ≡ false
physicalRateWeightedR225CollapseUsesPointwiseSeparationIsFalse = refl

physicalRateWeightedR225CollapseIntroducesEstimateIsFalse :
  physicalRateWeightedR225CollapseIntroducesEstimate ≡ false
physicalRateWeightedR225CollapseIntroducesEstimateIsFalse = refl
