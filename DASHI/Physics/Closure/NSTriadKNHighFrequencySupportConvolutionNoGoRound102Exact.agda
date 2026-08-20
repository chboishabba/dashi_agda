module DASHI.Physics.Closure.NSTriadKNHighFrequencySupportConvolutionNoGoRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / RECONNAISSANCE BOUNDARY
--
-- Author: Luca Eliseo Pavesi.
-- Title: "Global Regularity for the Three-Dimensional Incompressible
-- Navier-Stokes Equations via Geometric Frustration and Helical
-- Quasi-Trapping".
-- Version/year: Zenodo v3, 4 July 2026.
-- DOI: 10.5281/zenodo.21194906.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND102 / HIGH-FREQUENCY SUPPORT IS NOT CONVOLUTION-CLOSED
--
-- A recent unreviewed preprint motivates a 1/K spectral-flux estimate by
-- describing the high-frequency support V_K as essentially cross-closed.
-- Before using that idea, this module checks the underlying lattice claim.
--
-- At unit cutoff take the exact resonant triad
--
--   p = ( 2,0,0),   q = (-2,1,0),   k = (0,1,0).
--
-- Then p+q=k, while the literal integer squared norms are
--
--   |p|^2 = 4,   |q|^2 = 5,   |k|^2 = 1.
--
-- Hence both inputs lie strictly above the unit cutoff while the output lies
-- on/below it.  High Fourier support is therefore not closed under convolution
-- addition.  Any genuine quasi-trapping theorem must use coefficient-level
-- cancellation/decay, amplitude structure, or a proved lattice-sum estimate;
-- support geometry alone cannot supply it.
--
-- This is consistent with the Round93/102 Waleffe analysis: for this family the
-- helical majority-radius DIFFERENCE may be small even though the incidence is
-- present.  The plausible gain is in the coefficient, not in nonexistence of
-- high-high-to-low triads.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as Norm

p q k : Z3.FourierMode
p = Z3.mode (+ 2) (+ 0) (+ 0)
q = Z3.mode (-[1+ 1 ]) (+ 1) (+ 0)
k = Z3.mode (+ 0) (+ 1) (+ 0)

resonance : Z3.addMode p q ≡ k
resonance = refl

pNormSquaredIsFour : Norm.modeNatNormSquared p ≡ 4
pNormSquaredIsFour = refl

qNormSquaredIsFive : Norm.modeNatNormSquared q ≡ 5
qNormSquaredIsFive = refl

kNormSquaredIsOne : Norm.modeNatNormSquared k ≡ 1
kNormSquaredIsOne = refl

HighAtUnit : Z3.FourierMode → Set
HighAtUnit mode = 2 ≤ Norm.modeNatNormSquared mode

LowAtUnit : Z3.FourierMode → Set
LowAtUnit mode = Norm.modeNatNormSquared mode ≤ 1

pHigh : HighAtUnit p
pHigh = s≤s (s≤s z≤n)

qHigh : HighAtUnit q
qHigh = s≤s (s≤s z≤n)

kLow : LowAtUnit k
kLow = s≤s z≤n

record HighSupportConvolutionClosed : Set where
  field
    closesHigh :
      (left right output : Z3.FourierMode) →
      Z3.addMode left right ≡ output →
      HighAtUnit left → HighAtUnit right →
      HighAtUnit output

open HighSupportConvolutionClosed public

twoNotLeOne : 2 ≤ 1 → ⊥
twoNotLeOne (s≤s ())

unitHighSupportCannotBeConvolutionClosed :
  HighSupportConvolutionClosed → ⊥
unitHighSupportCannotBeConvolutionClosed closure =
  twoNotLeOne (closesHigh closure p q k resonance pHigh qHigh)

round102HighFrequencySupportConvolutionClosed : Bool
round102HighFrequencySupportConvolutionClosed = false

round102HighHighToLowIncidenceExistsAtUnitCutoff : Bool
round102HighHighToLowIncidenceExistsAtUnitCutoff = true

round102HighFrequencySupportConvolutionClosedIsFalse :
  round102HighFrequencySupportConvolutionClosed ≡ false
round102HighFrequencySupportConvolutionClosedIsFalse = refl

round102HighHighToLowIncidenceExistsAtUnitCutoffIsTrue :
  round102HighHighToLowIncidenceExistsAtUnitCutoff ≡ true
round102HighHighToLowIncidenceExistsAtUnitCutoffIsTrue = refl
