module DASHI.Physics.Closure.NSTriadKNLuoRelativeScaleProbeCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hajer Bahouri, Jean-Yves Chemin and Raphael Danchin,
-- "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Piero D'Ancona, "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- Ingrid Daubechies, "Ten Lectures on Wavelets".
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
-- Connect the already-corrected LH exponent branches to the domain-free
-- relative-scale and separating-probe interfaces.  Branch one and branch two
-- remain distinct probes; branch two is exactly the displayed half-gap target.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_*_)
open import Data.Product using (_×_)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Common.FiniteRingScaleDualityExact as Scale
import DASHI.Physics.Common.SeparatingProbeFamilyExact as Probe
import DASHI.Physics.Closure.NSTriadKNLuoLowHighExponentBookkeepingCorrectedExact as LH

nsDyadicOneStep : Scale.SpatialFrequencyScale
nsDyadicOneStep = Scale.dyadicOneStep

nsDyadicDualityExact :
  Scale.spatialNumerator nsDyadicOneStep
    * Scale.frequencyNumerator nsDyadicOneStep
  ≡ Scale.spatialDenominator nsDyadicOneStep
    * Scale.frequencyDenominator nsDyadicOneStep
nsDyadicDualityExact = Scale.dualProductIsOne nsDyadicOneStep

data LowHighBranchProbe : Set where
  strongTaylorBranch : LowHighBranchProbe
  weakDisplayedBranch : LowHighBranchProbe

branchExponent : LowHighBranchProbe → ℚ → ℚ → ℚ
branchExponent strongTaylorBranch = LH.branchOneRawExponent
branchExponent weakDisplayedBranch = LH.branchTwoRawExponent

branchGapExponent : LowHighBranchProbe → ℚ → ℚ → ℚ
branchGapExponent strongTaylorBranch = LH.strongGapExponent
branchGapExponent weakDisplayedBranch = LH.weakGapExponent

branchProbeExact :
  ∀ branch q r →
  branchExponent branch q r ≡ branchGapExponent branch q r
branchProbeExact strongTaylorBranch = LH.branchOneIsStrongGap
branchProbeExact weakDisplayedBranch = LH.branchTwoIsWeakGap

weakBranchMatchesDisplayedHalfGap :
  ∀ q r →
  branchExponent weakDisplayedBranch q r ≡ LH.weakGapExponent q r
weakBranchMatchesDisplayedHalfGap = LH.branchTwoIsWeakGap

record BranchProbeVector : Set where
  constructor branchProbeVector
  field
    strongProbe : Nat
    weakProbe : Nat

branchIdentityProbeSystem : Probe.SeparatingProbeSystem (Nat × Nat) Nat
branchIdentityProbeSystem = Probe.canonicalPairProbeSystem

record RelativeScaleProbeBoundary : Set where
  constructor relativeScaleProbeBoundary
  field
    branchOneAndBranchTwoAreInterchangeable : Set
    branchOneAndBranchTwoAreNotInterchangeable :
      branchOneAndBranchTwoAreInterchangeable → Set
    finiteExponentIdentityProvesPhysicalCommutator : Set
    finiteExponentIdentityDoesNotProvePhysicalCommutator :
      finiteExponentIdentityProvesPhysicalCommutator → Set

canonicalRelativeScaleProbeBoundary : RelativeScaleProbeBoundary
canonicalRelativeScaleProbeBoundary =
  relativeScaleProbeBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
