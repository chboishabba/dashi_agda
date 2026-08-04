module DASHI.Physics.Closure.NSTriadKNLuoFourResidueBlockDecayExact where

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
-- PURPOSE
-- Carry the explicit b=4 contraction through all four residue classes.  A
-- proof-relevant path stores only the one-block inequalities
--
--   E_{r+4(k+1)} <= (1/2) E_{r+4k}.
--
-- Induction derives
--
--   E_{r+4k} <= (1/2)^k E_r
--
-- for each r=0,1,2,3.  The terminal decay theorem is therefore not a field of
-- the input package.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Rational using (ℚ; 1ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesFourShiftBootstrapExact as Bootstrap

half : ℚ
half = + 1 / 2

halfPower : Nat → ℚ
halfPower zero = 1ℚ
halfPower (suc n) = half * halfPower n

data HalfContractionPath : ℚ → Nat → ℚ → Set where
  start : (energy : ℚ) → HalfContractionPath energy zero energy

  contract :
    ∀ {initial steps current next} →
    HalfContractionPath initial steps current →
    next ≤ half * current →
    HalfContractionPath initial (suc steps) next

halfContractionPathBound :
  ∀ {initial steps terminal} →
  HalfContractionPath initial steps terminal →
  terminal ≤ halfPower steps * initial
halfContractionPathBound (start energy) =
  subst
    (λ right → energy ≤ right)
    (ℚₚ.*-identityˡ energy)
    ℚₚ.≤-refl
halfContractionPathBound
  (contract {current = current} path nextBound) =
  let
    induction = halfContractionPathBound path

    scaledInduction :
      half * current
      ≤ half * (halfPower _ * _)
    scaledInduction =
      ℚₚ.*-monoˡ-≤-nonNeg
        half
        induction

    reassociate :
      half * (halfPower _ * _)
      ≡ halfPower (suc _) * _
    reassociate = refl
  in
  ℚₚ.≤-trans
    nextBound
    (subst
      (λ right → half * current ≤ right)
      reassociate
      scaledInduction)

alignedShell : Nat → Nat → Nat
alignedShell residue block = residue + Alpha.fourTimes block

record FourResidueBlockDecayData : Set₁ where
  field
    energyAt : Nat → ℚ
    baseEnergy : Nat → ℚ

    baseMeaning :
      (residue : Nat) →
      energyAt (alignedShell residue zero) ≡ baseEnergy residue

    pathAt :
      (residue block : Nat) →
      HalfContractionPath
        (baseEnergy residue)
        block
        (energyAt (alignedShell residue block))

open FourResidueBlockDecayData public

alignedBlockDecay :
  (data : FourResidueBlockDecayData) →
  (residue block : Nat) →
  energyAt data (alignedShell residue block)
  ≤ halfPower block * baseEnergy data residue
alignedBlockDecay data residue block =
  halfContractionPathBound (pathAt data residue block)

zeroResidueDecay :
  (data : FourResidueBlockDecayData) →
  (block : Nat) →
  energyAt data (alignedShell zero block)
  ≤ halfPower block * baseEnergy data zero
zeroResidueDecay data = alignedBlockDecay data zero

oneResidueDecay :
  (data : FourResidueBlockDecayData) →
  (block : Nat) →
  energyAt data (alignedShell (suc zero) block)
  ≤ halfPower block * baseEnergy data (suc zero)
oneResidueDecay data = alignedBlockDecay data (suc zero)

twoResidueDecay :
  (data : FourResidueBlockDecayData) →
  (block : Nat) →
  energyAt data (alignedShell (suc (suc zero)) block)
  ≤ halfPower block * baseEnergy data (suc (suc zero))
twoResidueDecay data = alignedBlockDecay data (suc (suc zero))

threeResidueDecay :
  (data : FourResidueBlockDecayData) →
  (block : Nat) →
  energyAt data (alignedShell (suc (suc (suc zero))) block)
  ≤ halfPower block * baseEnergy data (suc (suc (suc zero)))
threeResidueDecay data = alignedBlockDecay data (suc (suc (suc zero)))

explicitBootstrapCoefficientFitsHalf :
  Bootstrap.combinedCoefficient ≤ half
explicitBootstrapCoefficientFitsHalf =
  Bootstrap.combinedCoefficientBelowHalf
