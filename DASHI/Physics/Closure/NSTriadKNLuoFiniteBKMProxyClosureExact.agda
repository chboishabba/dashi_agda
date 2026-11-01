module DASHI.Physics.Closure.NSTriadKNLuoFiniteBKMProxyClosureExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Close the finite final composition rather than merely name its endpoints.
-- A vorticity-time proxy is supplied at every aligned shell and is required
-- pointwise to lie below the already-constructed weighted criterion.  Exact
-- finite summation then yields
--
--   proxy prefix <= weighted prefix
--                <= (4/3) (A_0+A_1+A_2+A_3).
--
-- The missing continuum theorem is isolated to identifying the genuine
-- integral of ||omega(t)||_infinity with such a proxy uniformly in the shell
-- cutoff and terminal time.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNLuoFourResidueBlockDecayExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourResidueSummabilityExact as Sum
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

record FiniteBKMProxyData : Set₁ where
  field
    contractionFamily : Four.FourResidueBlockRecursionFamily
    vorticityTimeProxyAt : Nat → ℚ

    proxyBelowCriterion :
      (residue block : Nat) →
      vorticityTimeProxyAt (Four.alignedShell residue block)
      ≤ Four.weightedCriterionAt contractionFamily
          (Four.alignedShell residue block)

open FiniteBKMProxyData public

sumAlignedProxy :
  FiniteBKMProxyData → Nat → Nat → ℚ
sumAlignedProxy proxyData residue zero =
  vorticityTimeProxyAt proxyData (Four.alignedShell residue zero)
sumAlignedProxy proxyData residue (suc block) =
  vorticityTimeProxyAt proxyData
      (Four.alignedShell residue (suc block))
  + sumAlignedProxy proxyData residue block

sumAlignedProxyBelowCriterion :
  (proxyData : FiniteBKMProxyData) →
  (residue block : Nat) →
  sumAlignedProxy proxyData residue block
  ≤ Sum.sumAlignedBlocks
      (contractionFamily proxyData) residue block
sumAlignedProxyBelowCriterion proxyData residue zero =
  proxyBelowCriterion proxyData residue zero
sumAlignedProxyBelowCriterion proxyData residue (suc block) =
  ℚₚ.+-mono-≤
    (proxyBelowCriterion proxyData residue (suc block))
    (sumAlignedProxyBelowCriterion proxyData residue block)

fourResidueProxyPrefix : FiniteBKMProxyData → Nat → ℚ
fourResidueProxyPrefix proxyData block =
  sumAlignedProxy proxyData zero block
  + sumAlignedProxy proxyData (suc zero) block
  + sumAlignedProxy proxyData (suc (suc zero)) block
  + sumAlignedProxy proxyData (suc (suc (suc zero))) block

fourResidueProxyBelowCriterionPrefix :
  (proxyData : FiniteBKMProxyData) →
  (block : Nat) →
  fourResidueProxyPrefix proxyData block
  ≤ Sum.fourResiduePrefix (contractionFamily proxyData) block
fourResidueProxyBelowCriterionPrefix proxyData block =
  ℚₚ.+-mono-≤
    (ℚₚ.+-mono-≤
      (ℚₚ.+-mono-≤
        (sumAlignedProxyBelowCriterion proxyData zero block)
        (sumAlignedProxyBelowCriterion proxyData (suc zero) block))
      (sumAlignedProxyBelowCriterion
        proxyData (suc (suc zero)) block))
    (sumAlignedProxyBelowCriterion
      proxyData (suc (suc (suc zero))) block)

finiteBKMProxyUniformBound :
  (proxyData : FiniteBKMProxyData) →
  (block : Nat) →
  0ℚ ≤ Four.baseCriterion (contractionFamily proxyData) zero →
  0ℚ ≤ Four.baseCriterion (contractionFamily proxyData) (suc zero) →
  0ℚ ≤ Four.baseCriterion
    (contractionFamily proxyData) (suc (suc zero)) →
  0ℚ ≤ Four.baseCriterion
    (contractionFamily proxyData) (suc (suc (suc zero))) →
  fourResidueProxyPrefix proxyData block
  ≤ Geo.fourThirds
      * Sum.fourBaseTotal (contractionFamily proxyData)
finiteBKMProxyUniformBound
  proxyData block base0 base1 base2 base3 =
  ℚₚ.≤-trans
    (fourResidueProxyBelowCriterionPrefix proxyData block)
    (Sum.fourResidueUniformSummability
      (contractionFamily proxyData)
      block base0 base1 base2 base3)
