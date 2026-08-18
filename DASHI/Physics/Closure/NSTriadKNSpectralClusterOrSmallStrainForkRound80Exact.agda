module DASHI.Physics.Closure.NSTriadKNSpectralClusterOrSmallStrainForkRound80Exact where

------------------------------------------------------------------------
-- ROUND80 / TOTAL C4 SPECTRAL FORK
--
-- Davis--Kahan needs separation only between the selected spectral CLUSTER and
-- its complement.  In 3D there are two adjacent strain gaps.  For any chosen
-- threshold delta, total rational order gives a three-way exhaustive fork:
--
--   delta <= g12;                    -- top line vs lower 2D cluster separated
--   delta <= g23;                    -- upper 2D cluster vs bottom line separated
--   g12 <= delta and g23 <= delta.   -- both gaps small
--
-- The final branch is not an unclassified degeneracy.  By the exact trace-free
-- gap reconstruction in Round80, both gaps control the entire strain spectrum.
-- Thus C4 can be reformulated as:
--
--   separated cluster projector turnover
--   OR separated complementary cluster projector turnover
--   OR small-strain-spectrum depletion/weak-stretching estimate.
--
-- This avoids demanding a uniformly simple eigenframe at every selected event.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Sum.Base using (inj₁; inj₂)

import DASHI.Physics.Closure.NSTriadKNTraceFreeGapSpectrumRound80Exact as Spectrum

data SpectralClusterOrSmallStrainFork
    (spectrum : Spectrum.ThreeSpectrum)
    (threshold : ℚ) : Set where
  gap12SeparatesTopFromLowerCluster :
    threshold ≤ Spectrum.gap12 spectrum →
    SpectralClusterOrSmallStrainFork spectrum threshold

  gap23SeparatesUpperClusterFromBottom :
    threshold ≤ Spectrum.gap23 spectrum →
    SpectralClusterOrSmallStrainFork spectrum threshold

  bothAdjacentGapsSmall :
    Spectrum.gap12 spectrum ≤ threshold →
    Spectrum.gap23 spectrum ≤ threshold →
    SpectralClusterOrSmallStrainFork spectrum threshold

spectralClusterOrSmallStrainForkTotal :
  (spectrum : Spectrum.ThreeSpectrum) →
  (threshold : ℚ) →
  SpectralClusterOrSmallStrainFork spectrum threshold
spectralClusterOrSmallStrainForkTotal spectrum threshold
  with ℚP.≤-total threshold (Spectrum.gap12 spectrum)
... | inj₁ threshold≤gap12 =
  gap12SeparatesTopFromLowerCluster threshold≤gap12
... | inj₂ gap12≤threshold
  with ℚP.≤-total threshold (Spectrum.gap23 spectrum)
...   | inj₁ threshold≤gap23 =
  gap23SeparatesUpperClusterFromBottom threshold≤gap23
...   | inj₂ gap23≤threshold =
  bothAdjacentGapsSmall gap12≤threshold gap23≤threshold

record TraceFreeSmallGapBranch (threshold : ℚ) : Set where
  constructor trace-free-small-gap-branch
  field
    traceFreeSpectrum : Spectrum.TraceFreeThreeSpectrum
    gap12Small :
      Spectrum.gap12 (Spectrum.spectrum traceFreeSpectrum) ≤ threshold
    gap23Small :
      Spectrum.gap23 (Spectrum.spectrum traceFreeSpectrum) ≤ threshold

open TraceFreeSmallGapBranch public

-- The exact reconstruction equalities are exported on the small-gap branch;
-- the next physical theorem may turn these into an operator/stretching bound
-- without choosing any individual eigenvector through a degeneracy.
smallGapBranchLambda1Identity :
  ∀ {threshold} (branch : TraceFreeSmallGapBranch threshold) →
  Spectrum.three * Spectrum.lambda1 (Spectrum.spectrum (traceFreeSpectrum branch))
  ≡ Spectrum.two * Spectrum.gap12 (Spectrum.spectrum (traceFreeSpectrum branch))
    + Spectrum.gap23 (Spectrum.spectrum (traceFreeSpectrum branch))
smallGapBranchLambda1Identity branch =
  Spectrum.traceFreeLambda1FromGaps (traceFreeSpectrum branch)
  where
  open import Data.Rational.Base using (_+_; _*_)

round80UniformSimpleEigenframeNoLongerRequiredByC4Architecture : Bool
round80UniformSimpleEigenframeNoLongerRequiredByC4Architecture = true

round80C4HasSeparatedClusterOrSmallSpectrumFork : Bool
round80C4HasSeparatedClusterOrSmallSpectrumFork = true

round80C4HasSeparatedClusterOrSmallSpectrumForkIsTrue :
  round80C4HasSeparatedClusterOrSmallSpectrumFork ≡ true
round80C4HasSeparatedClusterOrSmallSpectrumForkIsTrue = refl
