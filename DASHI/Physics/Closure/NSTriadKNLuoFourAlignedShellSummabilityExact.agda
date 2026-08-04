module DASHI.Physics.Closure.NSTriadKNLuoFourAlignedShellSummabilityExact where

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
-- Prove the exact summability calculation for all four residue classes of a
-- four-aligned shell bootstrap.  If each residue class satisfies
--
--   S_r(n) <= C (1/4)^n,   r=0,1,2,3,
--
-- then every finite prefix of the complete four-class sum is bounded by
--
--   (16/3) C.
--
-- This is the all-residue arithmetic needed after block decay.  The theorem
-- is uniform in the finite cutoff and does not assume the final prefix bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant

four sixteenThirds : ℚ
four = Int.+ 4 / 1
sixteenThirds = Int.+ 16 / 3

fourNonnegative : 0ℚ ≤ four
fourNonnegative = toWitness {a? = 0ℚ ≤? four} _

record FourAlignedShellDecay : Set where
  constructor four-aligned-shell-decay
  field
    constant : ℚ
    constantNonnegative : 0ℚ ≤ constant

    residue0 residue1 residue2 residue3 : Nat → ℚ

    residue0Bound :
      (block : Nat) →
      residue0 block ≤ constant * Geo.pow Geo.quarter block
    residue1Bound :
      (block : Nat) →
      residue1 block ≤ constant * Geo.pow Geo.quarter block
    residue2Bound :
      (block : Nat) →
      residue2 block ≤ constant * Geo.pow Geo.quarter block
    residue3Bound :
      (block : Nat) →
      residue3 block ≤ constant * Geo.pow Geo.quarter block

open FourAlignedShellDecay public

blockTarget : FourAlignedShellDecay → Nat → ℚ
blockTarget data block =
  constant data * Geo.pow Geo.quarter block

fourClassBlockTotal : FourAlignedShellDecay → Nat → ℚ
fourClassBlockTotal data block =
  residue0 data block
  + residue1 data block
  + residue2 data block
  + residue3 data block

fourClassBlockBound :
  (data : FourAlignedShellDecay) →
  (block : Nat) →
  fourClassBlockTotal data block
  ≤ four * blockTarget data block
fourClassBlockBound data block =
  let
    target = blockTarget data block

    combined :
      residue0 data block
      + residue1 data block
      + residue2 data block
      + residue3 data block
      ≤ target + target + target + target
    combined =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (ℚₚ.+-mono-≤
            (residue0Bound data block)
            (residue1Bound data block))
          (residue2Bound data block))
        (residue3Bound data block)

    targetMeaning :
      target + target + target + target ≡ four * target
    targetMeaning = solve (target ∷ [])
  in
  subst
    (λ upper → fourClassBlockTotal data block ≤ upper)
    targetMeaning
    combined

fourConstant : FourAlignedShellDecay → ℚ
fourConstant data = four * constant data

fourConstantNonnegative :
  (data : FourAlignedShellDecay) →
  0ℚ ≤ fourConstant data
fourConstantNonnegative data =
  let
    instance
      fourIsNonnegative = nonNegative fourNonnegative
      constantIsNonnegative = nonNegative (constantNonnegative data)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg four (constant data)
  in
  ℚₚ.nonNegative⁻¹ (fourConstant data)

fourClassPrefix : FourAlignedShellDecay → Nat → ℚ
fourClassPrefix data cutoff =
  Majorant.sumTo (fourClassBlockTotal data) cutoff

fourClassPrefixToGeometric :
  (data : FourAlignedShellDecay) →
  (cutoff : Nat) →
  fourClassPrefix data cutoff
  ≤ fourConstant data * Geo.partialSum Geo.quarter cutoff
fourClassPrefixToGeometric data cutoff =
  let
    termwise :
      fourClassPrefix data cutoff
      ≤ Majorant.sumTo
          (λ block → fourConstant data * Geo.pow Geo.quarter block)
          cutoff
    termwise =
      Majorant.sumToMonotone
        (fourClassBlockTotal data)
        (λ block → fourConstant data * Geo.pow Geo.quarter block)
        cutoff
        (λ block →
          subst
            (λ upper → fourClassBlockTotal data block ≤ upper)
            (solve
              ( four
              ∷ constant data
              ∷ Geo.pow Geo.quarter block
              ∷ []
              ))
            (fourClassBlockBound data block))

    scaledPowerMeaning :
      Majorant.sumTo
        (λ block → fourConstant data * Geo.pow Geo.quarter block)
        cutoff
      ≡ fourConstant data
          * Majorant.sumTo (Geo.pow Geo.quarter) cutoff
    scaledPowerMeaning =
      Majorant.scaleSum
        (fourConstant data)
        (Geo.pow Geo.quarter)
        cutoff

    partialSumMeaning :
      Majorant.sumTo (Geo.pow Geo.quarter) cutoff
      ≡ Geo.partialSum Geo.quarter cutoff
    partialSumMeaning = Majorant.powerSumMeaning Geo.quarter cutoff
  in
  subst
    (λ upper → fourClassPrefix data cutoff ≤ upper)
    (trans scaledPowerMeaning
      (cong (fourConstant data *_) partialSumMeaning))
    termwise

fourClassPrefixBound :
  (data : FourAlignedShellDecay) →
  (cutoff : Nat) →
  fourClassPrefix data cutoff
  ≤ sixteenThirds * constant data
fourClassPrefixBound data cutoff =
  let
    firstStep = fourClassPrefixToGeometric data cutoff

    geometricStep :
      fourConstant data * Geo.partialSum Geo.quarter cutoff
      ≤ fourConstant data * Geo.fourThirds
    geometricStep =
      let instance fourConstantIsNonnegative =
        nonNegative (fourConstantNonnegative data)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (fourConstant data)
        (Geo.quarterPartialSumBound cutoff)

    constantIdentity :
      fourConstant data * Geo.fourThirds
      ≡ sixteenThirds * constant data
    constantIdentity =
      solve (constant data ∷ [])
  in
  subst
    (λ upper → fourClassPrefix data cutoff ≤ upper)
    constantIdentity
    (ℚₚ.≤-trans firstStep geometricStep)

fourAlignedAllResiduesSummabilityClosed : Bool
fourAlignedAllResiduesSummabilityClosed = true

fourAlignedUniformPrefixConstantExact : Bool
fourAlignedUniformPrefixConstantExact = true

fourAlignedAllResiduesSummabilityClosedIsTrue :
  fourAlignedAllResiduesSummabilityClosed ≡ true
fourAlignedAllResiduesSummabilityClosedIsTrue = refl

fourAlignedUniformPrefixConstantExactIsTrue :
  fourAlignedUniformPrefixConstantExact ≡ true
fourAlignedUniformPrefixConstantExactIsTrue = refl
