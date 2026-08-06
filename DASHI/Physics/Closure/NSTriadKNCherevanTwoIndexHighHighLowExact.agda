module DASHI.Physics.Closure.NSTriadKNCherevanTwoIndexHighHighLowExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- Related paraproduct reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Make the two frequency indices of a genuine high--high to low interaction
-- literal.  The output shell q and high input shell p are related by
--
--   p = q + 1 + gap.
--
-- They cannot be represented by one shell variable in a nontrivial gap.
-- The source preprint defines R_N with P_N on the output, but later reuses
-- lambda as the high input scale and imposes a much lower output cutoff.
-- This module provides the exact indexing carrier required before those
-- formulas can be compared.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

record HighHighLowIndex : Set where
  constructor high-high-low-index
  field
    outputShell : Nat
    gap : Nat

open HighHighLowIndex public

inputShell : HighHighLowIndex → Nat
inputShell index = outputShell index + suc (gap index)

inputShellMeaning :
  (index : HighHighLowIndex) →
  inputShell index ≡ outputShell index + suc (gap index)
inputShellMeaning index = refl

firstOffDiagonal : HighHighLowIndex
firstOffDiagonal = high-high-low-index zero zero

firstOffDiagonalOutput :
  outputShell firstOffDiagonal ≡ zero
firstOffDiagonalOutput = refl

firstOffDiagonalInput :
  inputShell firstOffDiagonal ≡ suc zero
firstOffDiagonalInput = refl

firstOffDiagonalInputIsNotOutput :
  inputShell firstOffDiagonal ≢ outputShell firstOffDiagonal
firstOffDiagonalInputIsNotOutput ()

data OutputScaleRegime : Set where
  dyadicAnnularOutput : OutputScaleRegime
  belowUnitCutoff : OutputScaleRegime

projectedDyadRegime : OutputScaleRegime
projectedDyadRegime = dyadicAnnularOutput

negativePowerCutoffRegime : OutputScaleRegime
negativePowerCutoffRegime = belowUnitCutoff

annularOutputIsNotSubunitCutoff :
  projectedDyadRegime ≢ negativePowerCutoffRegime
annularOutputIsNotSubunitCutoff ()
