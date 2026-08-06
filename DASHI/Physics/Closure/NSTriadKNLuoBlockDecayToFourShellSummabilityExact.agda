module DASHI.Physics.Closure.NSTriadKNLuoBlockDecayToFourShellSummabilityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Connect the repository's proved fixed-block induction to all four shell
-- residue classes.  A block certificate with r=1/4 controls one block
-- sequence.  If each of the four physical shell quantities in that block is
-- below the block sequence, then every residue class has quarter-geometric
-- decay and the complete finite prefix is bounded by (16/3) C.
--
-- The power-function agreement and all order composition are proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNLuoFourAlignedShellSummabilityExact as Four

blockPowerMatchesGeometricPower :
  (ratio : ℚ) →
  (exponent : Nat) →
  Block.power ratio exponent ≡ Geo.pow ratio exponent
blockPowerMatchesGeometricPower ratio zero = refl
blockPowerMatchesGeometricPower ratio (suc exponent)
  rewrite blockPowerMatchesGeometricPower ratio exponent = refl

record BlockDecayToFourShellData : Set where
  constructor block-to-four-shell
  field
    certificate : Block.RationalFixedBlockDecay
    ratioIsQuarter : Block.r certificate ≡ Geo.quarter

    residue0 residue1 residue2 residue3 : Nat → ℚ

    residue0BelowBlock :
      (block : Nat) →
      residue0 block ≤ Block.sequence certificate block
    residue1BelowBlock :
      (block : Nat) →
      residue1 block ≤ Block.sequence certificate block
    residue2BelowBlock :
      (block : Nat) →
      residue2 block ≤ Block.sequence certificate block
    residue3BelowBlock :
      (block : Nat) →
      residue3 block ≤ Block.sequence certificate block

open BlockDecayToFourShellData public

blockTargetIsQuarterTarget :
  (data : BlockDecayToFourShellData) →
  (block : Nat) →
  Block.scaledTarget
    (Block.constant (certificate data))
    (Block.r (certificate data))
    block
  ≡ Block.constant (certificate data)
      * Geo.pow Geo.quarter block
blockTargetIsQuarterTarget data block
  rewrite ratioIsQuarter data
        | blockPowerMatchesGeometricPower Geo.quarter block = refl

residue0QuarterDecay :
  (data : BlockDecayToFourShellData) →
  (block : Nat) →
  residue0 data block
  ≤ Block.constant (certificate data) * Geo.pow Geo.quarter block
residue0QuarterDecay data block =
  subst
    (λ upper → residue0 data block ≤ upper)
    (blockTargetIsQuarterTarget data block)
    (ℚₚ.≤-trans
      (residue0BelowBlock data block)
      (Block.fixedBlockDecay (certificate data) block))

residue1QuarterDecay :
  (data : BlockDecayToFourShellData) →
  (block : Nat) →
  residue1 data block
  ≤ Block.constant (certificate data) * Geo.pow Geo.quarter block
residue1QuarterDecay data block =
  subst
    (λ upper → residue1 data block ≤ upper)
    (blockTargetIsQuarterTarget data block)
    (ℚₚ.≤-trans
      (residue1BelowBlock data block)
      (Block.fixedBlockDecay (certificate data) block))

residue2QuarterDecay :
  (data : BlockDecayToFourShellData) →
  (block : Nat) →
  residue2 data block
  ≤ Block.constant (certificate data) * Geo.pow Geo.quarter block
residue2QuarterDecay data block =
  subst
    (λ upper → residue2 data block ≤ upper)
    (blockTargetIsQuarterTarget data block)
    (ℚₚ.≤-trans
      (residue2BelowBlock data block)
      (Block.fixedBlockDecay (certificate data) block))

residue3QuarterDecay :
  (data : BlockDecayToFourShellData) →
  (block : Nat) →
  residue3 data block
  ≤ Block.constant (certificate data) * Geo.pow Geo.quarter block
residue3QuarterDecay data block =
  subst
    (λ upper → residue3 data block ≤ upper)
    (blockTargetIsQuarterTarget data block)
    (ℚₚ.≤-trans
      (residue3BelowBlock data block)
      (Block.fixedBlockDecay (certificate data) block))

fourAlignedShellDecayFromBlock :
  BlockDecayToFourShellData → Four.FourAlignedShellDecay
fourAlignedShellDecayFromBlock data =
  Four.four-aligned-shell-decay
    (Block.constant (certificate data))
    (Block.constantNonnegative (certificate data))
    (residue0 data)
    (residue1 data)
    (residue2 data)
    (residue3 data)
    (residue0QuarterDecay data)
    (residue1QuarterDecay data)
    (residue2QuarterDecay data)
    (residue3QuarterDecay data)

blockDecayAllFourShellPrefixBound :
  (data : BlockDecayToFourShellData) →
  (cutoff : Nat) →
  Four.fourClassPrefix
    (fourAlignedShellDecayFromBlock data)
    cutoff
  ≤ Four.sixteenThirds * Block.constant (certificate data)
blockDecayAllFourShellPrefixBound data cutoff =
  Four.fourClassPrefixBound
    (fourAlignedShellDecayFromBlock data)
    cutoff

fixedBlockToAllFourResiduesClosed : Bool
fixedBlockToAllFourResiduesClosed = true

fixedBlockToUniformShellPrefixClosed : Bool
fixedBlockToUniformShellPrefixClosed = true

fixedBlockToAllFourResiduesClosedIsTrue :
  fixedBlockToAllFourResiduesClosed ≡ true
fixedBlockToAllFourResiduesClosedIsTrue = refl

fixedBlockToUniformShellPrefixClosedIsTrue :
  fixedBlockToUniformShellPrefixClosed ≡ true
fixedBlockToUniformShellPrefixClosedIsTrue = refl
