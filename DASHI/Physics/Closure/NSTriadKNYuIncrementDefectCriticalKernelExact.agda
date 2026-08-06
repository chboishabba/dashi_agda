module DASHI.Physics.Closure.NSTriadKNYuIncrementDefectCriticalKernelExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Authors: Francesca Da Lio; Tristan Rivière.
-- Title: "Three-Term Commutator Estimates and the Regularity of
-- 1/2-Harmonic Maps into Spheres".
-- DOI: 10.2140/apde.2011.4.149.
--
-- PURPOSE
-- Implement the finite critical-kernel form requested for the derivative-
-- compatible increment defect. The explicit kernel
--
--   kappa_m = (1/4)(1/4)^m
--
-- is pointwise dominated by the normalized annular kernel
--
--   h_m = (1/2)(1/2)^m.
--
-- Hence every finite increment convolution is dominated by the already
-- proved l1*c0 annular convolution, uniformly in the cutoff. A defect bounded
-- by this critical convolution therefore vanishes whenever the critical shell
-- source does.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact as HL
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit
import DASHI.Physics.Closure.NSTriadKNYuFiniteFarFieldConvolutionC0Exact as Far

incrementWeight : Nat → ℚ
incrementWeight offset = Geo.quarter * Geo.pow Geo.quarter offset

incrementWeightNonnegative :
  (offset : Nat) → 0ℚ ≤ incrementWeight offset
incrementWeightNonnegative offset =
  let
    powerNN = Geo.powNonnegative Geo.quarter offset Geo.quarterNonnegative
    instance
      quarterNNI = nonNegative Geo.quarterNonnegative
      powerNNI = nonNegative powerNN
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          Geo.quarter
          (Geo.pow Geo.quarter offset)
  in
  ℚₚ.nonNegative⁻¹ (incrementWeight offset)

quarterBelowHalf : Geo.quarter ≤ HL.half
quarterBelowHalf = toWitness {a? = Geo.quarter ≤? HL.half} _

quarterPowerBelowHalfPower :
  (offset : Nat) →
  Geo.pow Geo.quarter offset ≤ Geo.pow HL.half offset
quarterPowerBelowHalfPower zero = ℚₚ.≤-refl
quarterPowerBelowHalfPower (suc offset) =
  L2.nonnegativeProductMonotone
    Geo.quarterNonnegative
    (Geo.powNonnegative Geo.quarter offset Geo.quarterNonnegative)
    HL.halfNonnegative
    (Geo.powNonnegative HL.half offset HL.halfNonnegative)
    quarterBelowHalf
    (quarterPowerBelowHalfPower offset)

incrementWeightBelowAnnularWeight :
  (offset : Nat) →
  incrementWeight offset ≤ Far.annularWeight offset
incrementWeightBelowAnnularWeight offset =
  L2.nonnegativeProductMonotone
    Geo.quarterNonnegative
    (Geo.powNonnegative Geo.quarter offset Geo.quarterNonnegative)
    HL.halfNonnegative
    (Geo.powNonnegative HL.half offset HL.halfNonnegative)
    quarterBelowHalf
    (quarterPowerBelowHalfPower offset)

finiteIncrementConvolution :
  (criticalShell : Nat → ℚ) → Nat → Nat → ℚ
finiteIncrementConvolution criticalShell shell zero =
  incrementWeight zero * criticalShell shell
finiteIncrementConvolution criticalShell shell (suc cutoff) =
  finiteIncrementConvolution criticalShell shell cutoff
  + incrementWeight (suc cutoff)
    * criticalShell (shell + suc cutoff)

finiteIncrementBelowAnnular :
  (criticalShell : Nat → ℚ) →
  ((shell : Nat) → 0ℚ ≤ criticalShell shell) →
  (shell cutoff : Nat) →
  finiteIncrementConvolution criticalShell shell cutoff
  ≤ Far.finiteAnnularConvolution criticalShell shell cutoff
finiteIncrementBelowAnnular criticalShell criticalNN shell zero =
  L2.nonnegativeProductMonotone
    (incrementWeightNonnegative zero)
    (criticalNN shell)
    (Far.annularWeightNonnegative zero)
    (criticalNN shell)
    (incrementWeightBelowAnnularWeight zero)
    ℚₚ.≤-refl
finiteIncrementBelowAnnular criticalShell criticalNN shell (suc cutoff) =
  ℚₚ.+-mono-≤
    (finiteIncrementBelowAnnular criticalShell criticalNN shell cutoff)
    (L2.nonnegativeProductMonotone
      (incrementWeightNonnegative (suc cutoff))
      (criticalNN (shell + suc cutoff))
      (Far.annularWeightNonnegative (suc cutoff))
      (criticalNN (shell + suc cutoff))
      (incrementWeightBelowAnnularWeight (suc cutoff))
      ℚₚ.≤-refl)

record IncrementDefectCriticalKernelData : Set where
  constructor increment-defect-critical-kernel-data
  field
    criticalShell incrementDefect : Nat → ℚ
    annularCutoff : Nat

    criticalShellNonnegative :
      (shell : Nat) → 0ℚ ≤ criticalShell shell

    incrementDefectBound :
      (shell : Nat) →
      incrementDefect shell
      ≤ finiteIncrementConvolution criticalShell shell annularCutoff

open IncrementDefectCriticalKernelData public

incrementDefectBelowAnnularConvolution :
  (dataSet : IncrementDefectCriticalKernelData) →
  (shell : Nat) →
  incrementDefect dataSet shell
  ≤ Far.finiteAnnularConvolution
      (criticalShell dataSet)
      shell
      (annularCutoff dataSet)
incrementDefectBelowAnnularConvolution dataSet shell =
  ℚₚ.≤-trans
    (incrementDefectBound dataSet shell)
    (finiteIncrementBelowAnnular
      (criticalShell dataSet)
      (criticalShellNonnegative dataSet)
      shell
      (annularCutoff dataSet))

incrementDefectVanishingFromCriticalShell :
  (dataSet : IncrementDefectCriticalKernelData) →
  Limit.TendsToZero (criticalShell dataSet) →
  Limit.TendsToZero (incrementDefect dataSet)
incrementDefectVanishingFromCriticalShell dataSet criticalVanishing =
  let
    annularVanishing =
      Far.finiteAnnularConvolutionVanishing
        (criticalShell dataSet)
        (criticalShellNonnegative dataSet)
        criticalVanishing
        (annularCutoff dataSet)
  in
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (incrementDefect dataSet)
      (λ shell →
        Far.finiteAnnularConvolution
          (criticalShell dataSet)
          shell
          (annularCutoff dataSet))
      (incrementDefectBelowAnnularConvolution dataSet))
    annularVanishing
