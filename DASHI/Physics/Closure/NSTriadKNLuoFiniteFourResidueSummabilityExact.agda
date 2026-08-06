module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourResidueSummabilityExact where

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
-- Convert the already-derived four-shift contraction into an actual finite
-- summability theorem.  Along each residue class,
--
--   A_{r+4k} <= (1/4)^k A_r
--
-- implies that every finite block prefix is at most
--
--   (sum_{k=0}^N (1/4)^k) A_r <= (4/3) A_r.
--
-- Summing the four residue classes yields the explicit cutoff-uniform bound
--
--   total <= (4/3) (A_0+A_1+A_2+A_3).
--
-- The remaining continuum BKM step is now precisely the physical theorem
-- comparing the relevant vorticity integral to this weighted shell sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFourResidueBlockDecayExact as Four
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

quarterPowerAgreement :
  (block : Nat) →
  Four.quarterPower block ≡ Geo.pow Geo.quarter block
quarterPowerAgreement zero = refl
quarterPowerAgreement (suc block)
  rewrite quarterPowerAgreement block = refl

alignedBlockDecayGeo :
  (family : Four.FourResidueBlockRecursionFamily) →
  (residue block : Nat) →
  Four.weightedCriterionAt family (Four.alignedShell residue block)
  ≤ Geo.pow Geo.quarter block * Four.baseCriterion family residue
alignedBlockDecayGeo family residue block =
  subst
    (λ coefficient →
      Four.weightedCriterionAt family (Four.alignedShell residue block)
      ≤ coefficient * Four.baseCriterion family residue)
    (quarterPowerAgreement block)
    (Four.alignedBlockDecay family residue block)

sumAlignedBlocks :
  Four.FourResidueBlockRecursionFamily → Nat → Nat → ℚ
sumAlignedBlocks family residue zero =
  Four.weightedCriterionAt family (Four.alignedShell residue zero)
sumAlignedBlocks family residue (suc block) =
  Four.weightedCriterionAt family (Four.alignedShell residue (suc block))
  + sumAlignedBlocks family residue block

sumAlignedBlocksGeometricBound :
  (family : Four.FourResidueBlockRecursionFamily) →
  (residue block : Nat) →
  sumAlignedBlocks family residue block
  ≤ Geo.partialSum Geo.quarter block
      * Four.baseCriterion family residue
sumAlignedBlocksGeometricBound family residue zero
  rewrite Four.baseMeaning family residue =
  let
    rightMeaning :
      Geo.partialSum Geo.quarter zero * Four.baseCriterion family residue
      ≡ Four.baseCriterion family residue
    rightMeaning = solve (Four.baseCriterion family residue ∷ [])
  in
  subst
    (λ upper → Four.baseCriterion family residue ≤ upper)
    (sym rightMeaning)
    ℚₚ.≤-refl
sumAlignedBlocksGeometricBound family residue (suc block) =
  let
    combined :
      Four.weightedCriterionAt
          family (Four.alignedShell residue (suc block))
        + sumAlignedBlocks family residue block
      ≤ Geo.pow Geo.quarter (suc block)
          * Four.baseCriterion family residue
        + Geo.partialSum Geo.quarter block
          * Four.baseCriterion family residue
    combined =
      ℚₚ.+-mono-≤
        (alignedBlockDecayGeo family residue (suc block))
        (sumAlignedBlocksGeometricBound family residue block)

    targetMeaning :
      Geo.pow Geo.quarter (suc block)
          * Four.baseCriterion family residue
        + Geo.partialSum Geo.quarter block
          * Four.baseCriterion family residue
      ≡ Geo.partialSum Geo.quarter (suc block)
          * Four.baseCriterion family residue
    targetMeaning =
      solve
        ( Geo.pow Geo.quarter (suc block)
        ∷ Geo.partialSum Geo.quarter block
        ∷ Four.baseCriterion family residue
        ∷ []
        )
  in
  subst
    (λ upper → sumAlignedBlocks family residue (suc block) ≤ upper)
    targetMeaning
    combined

sumAlignedBlocksUniformBound :
  (family : Four.FourResidueBlockRecursionFamily) →
  (residue block : Nat) →
  0ℚ ≤ Four.baseCriterion family residue →
  sumAlignedBlocks family residue block
  ≤ Geo.fourThirds * Four.baseCriterion family residue
sumAlignedBlocksUniformBound family residue block baseNonnegative =
  let
    scaled :
      Geo.partialSum Geo.quarter block
        * Four.baseCriterion family residue
      ≤ Geo.fourThirds * Four.baseCriterion family residue
    scaled =
      let
        instance
          baseIsNonnegative = nonNegative baseNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Four.baseCriterion family residue)
        (Geo.quarterPartialSumBound block)
  in
  ℚₚ.≤-trans
    (sumAlignedBlocksGeometricBound family residue block)
    scaled

fourResiduePrefix :
  Four.FourResidueBlockRecursionFamily → Nat → ℚ
fourResiduePrefix family block =
  sumAlignedBlocks family zero block
  + sumAlignedBlocks family (suc zero) block
  + sumAlignedBlocks family (suc (suc zero)) block
  + sumAlignedBlocks family (suc (suc (suc zero))) block

fourBaseTotal : Four.FourResidueBlockRecursionFamily → ℚ
fourBaseTotal family =
  Four.baseCriterion family zero
  + Four.baseCriterion family (suc zero)
  + Four.baseCriterion family (suc (suc zero))
  + Four.baseCriterion family (suc (suc (suc zero)))

fourResidueUniformSummability :
  (family : Four.FourResidueBlockRecursionFamily) →
  (block : Nat) →
  0ℚ ≤ Four.baseCriterion family zero →
  0ℚ ≤ Four.baseCriterion family (suc zero) →
  0ℚ ≤ Four.baseCriterion family (suc (suc zero)) →
  0ℚ ≤ Four.baseCriterion family (suc (suc (suc zero))) →
  fourResiduePrefix family block
  ≤ Geo.fourThirds * fourBaseTotal family
fourResidueUniformSummability
  family block base0 base1 base2 base3 =
  let
    component =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (ℚₚ.+-mono-≤
            (sumAlignedBlocksUniformBound family zero block base0)
            (sumAlignedBlocksUniformBound family (suc zero) block base1))
          (sumAlignedBlocksUniformBound
            family (suc (suc zero)) block base2))
        (sumAlignedBlocksUniformBound
          family (suc (suc (suc zero))) block base3)

    targetMeaning :
      Geo.fourThirds * Four.baseCriterion family zero
      + Geo.fourThirds * Four.baseCriterion family (suc zero)
      + Geo.fourThirds * Four.baseCriterion family (suc (suc zero))
      + Geo.fourThirds
          * Four.baseCriterion family (suc (suc (suc zero)))
      ≡ Geo.fourThirds * fourBaseTotal family
    targetMeaning =
      solve
        ( Geo.fourThirds
        ∷ Four.baseCriterion family zero
        ∷ Four.baseCriterion family (suc zero)
        ∷ Four.baseCriterion family (suc (suc zero))
        ∷ Four.baseCriterion family (suc (suc (suc zero)))
        ∷ []
        )
  in
  subst
    (λ upper → fourResiduePrefix family block ≤ upper)
    targetMeaning
    component
