module DASHI.Physics.Closure.NSTriadKNLuoFiniteTerminalYoungSameConstantExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the finite terminal-window Young estimate with exactly the same
-- shell-independent kernel constant used in every pointwise spatial estimate.
-- No second terminal constant is introduced.  The proof is finite-sum
-- monotonicity plus the already-proved identity
--
--   sum_t C h_t = C sum_t h_t.
--
-- This closes the discrete terminal-window transport.  The continuum leaf is
-- only the passage from time Riemann/Bochner sums to the selected integral.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; -_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSignedConvolutionYoungExact as Young

record FiniteTerminalYoungData : Set where
  field
    smoothValue hardValue : Nat → ℚ
    timeCutoff : Nat
    kernelConstant : ℚ

    pointwiseUpper :
      (time : Nat) →
      smoothValue time ≤ kernelConstant * hardValue time

    pointwiseLower :
      (time : Nat) →
      - (kernelConstant * hardValue time) ≤ smoothValue time

open FiniteTerminalYoungData public

finiteTerminalYoungUpper :
  (data : FiniteTerminalYoungData) →
  Majorant.sumTo (smoothValue data) (timeCutoff data)
  ≤ kernelConstant data
    * Majorant.sumTo (hardValue data) (timeCutoff data)
finiteTerminalYoungUpper data =
  subst
    (λ upper →
      Majorant.sumTo (smoothValue data) (timeCutoff data)
      ≤ upper)
    (Majorant.scaleSum
      (kernelConstant data)
      (hardValue data)
      (timeCutoff data))
    (Majorant.sumToMonotone
      (smoothValue data)
      (λ time → kernelConstant data * hardValue data time)
      (timeCutoff data)
      (pointwiseUpper data))

finiteTerminalYoungLower :
  (data : FiniteTerminalYoungData) →
  - (kernelConstant data
      * Majorant.sumTo (hardValue data) (timeCutoff data))
  ≤ Majorant.sumTo (smoothValue data) (timeCutoff data)
finiteTerminalYoungLower data =
  subst
    (λ positiveSum →
      - positiveSum
      ≤ Majorant.sumTo (smoothValue data) (timeCutoff data))
    (Majorant.scaleSum
      (kernelConstant data)
      (hardValue data)
      (timeCutoff data))
    (Young.signedPrefixLower
      (smoothValue data)
      (λ time → kernelConstant data * hardValue data time)
      (timeCutoff data)
      (pointwiseLower data))

record FiniteSpatialYoungFamily : Set where
  field
    spatialData : Nat → Young.FiniteSignedConvolutionYoungData
    hardSup : Nat → ℚ
    timeCutoff : Nat
    commonKernelConstant : ℚ

    spatialBoundMeaning :
      (time : Nat) →
      Young.l1TimesSupBound (spatialData time)
      ≡ commonKernelConstant * hardSup time

open FiniteSpatialYoungFamily public

spatialSmoothValue : FiniteSpatialYoungFamily → Nat → ℚ
spatialSmoothValue family time =
  Majorant.sumTo
    (Young.signedTerm (spatialData family time))
    (Young.cutoff (spatialData family time))

spatialPointwiseUpper :
  (family : FiniteSpatialYoungFamily) →
  (time : Nat) →
  spatialSmoothValue family time
  ≤ commonKernelConstant family * hardSup family time
spatialPointwiseUpper family time =
  subst
    (λ upper → spatialSmoothValue family time ≤ upper)
    (spatialBoundMeaning family time)
    (Young.finiteConvolutionUpper (spatialData family time))

spatialPointwiseLower :
  (family : FiniteSpatialYoungFamily) →
  (time : Nat) →
  - (commonKernelConstant family * hardSup family time)
  ≤ spatialSmoothValue family time
spatialPointwiseLower family time =
  subst
    (λ bound → - bound ≤ spatialSmoothValue family time)
    (spatialBoundMeaning family time)
    (Young.finiteConvolutionLower (spatialData family time))

finiteSpatialFamilyTerminalData :
  FiniteSpatialYoungFamily → FiniteTerminalYoungData
finiteSpatialFamilyTerminalData family = record
  { smoothValue = spatialSmoothValue family
  ; hardValue = hardSup family
  ; timeCutoff = timeCutoff family
  ; kernelConstant = commonKernelConstant family
  ; pointwiseUpper = spatialPointwiseUpper family
  ; pointwiseLower = spatialPointwiseLower family
  }

finiteSpatialFamilyTerminalUpper :
  (family : FiniteSpatialYoungFamily) →
  Majorant.sumTo
    (spatialSmoothValue family)
    (timeCutoff family)
  ≤ commonKernelConstant family
    * Majorant.sumTo (hardSup family) (timeCutoff family)
finiteSpatialFamilyTerminalUpper family =
  finiteTerminalYoungUpper (finiteSpatialFamilyTerminalData family)

finiteSpatialFamilyTerminalLower :
  (family : FiniteSpatialYoungFamily) →
  - (commonKernelConstant family
      * Majorant.sumTo (hardSup family) (timeCutoff family))
  ≤ Majorant.sumTo
      (spatialSmoothValue family)
      (timeCutoff family)
finiteSpatialFamilyTerminalLower family =
  finiteTerminalYoungLower (finiteSpatialFamilyTerminalData family)

finiteTerminalYoungSameConstantClosed : Bool
finiteTerminalYoungSameConstantClosed = true

finiteSpatialToTerminalYoungTransportClosed : Bool
finiteSpatialToTerminalYoungTransportClosed = true

finiteTerminalYoungSameConstantClosedIsTrue :
  finiteTerminalYoungSameConstantClosed ≡ true
finiteTerminalYoungSameConstantClosedIsTrue = refl

finiteSpatialToTerminalYoungTransportClosedIsTrue :
  finiteSpatialToTerminalYoungTransportClosed ≡ true
finiteSpatialToTerminalYoungTransportClosedIsTrue = refl
