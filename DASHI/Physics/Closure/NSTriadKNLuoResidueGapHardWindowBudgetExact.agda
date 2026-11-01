module DASHI.Physics.Closure.NSTriadKNLuoResidueGapHardWindowBudgetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Transport the already-inhabited finite residue/operator/gap and forced-tail
-- majorant route into the rational hard-terminal-window budget consumed by the
-- non-circular official Luo closure.
--
-- This module proves the budget algebra. It deliberately keeps visible the
-- only load-bearing semantic seam: the Nat-valued cutoff majorant must be
-- identified with the actual hard low-pass gradient integral of the official
-- periodic solution, and its threshold must include the hard/smooth multiplier
-- constant. No terminal criterion is assumed as part of the physical carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat as ℕ
import Data.Rational.Base as ℚBase
open ℚBase using (ℚ; 0ℚ)

import DASHI.Physics.Closure.NSTriadKNResidueScaleOperatorGapExact as Gap
import DASHI.Physics.Closure.NSTriadKNLuoExplicitCutoffLocalizedCriterionExact as Cutoff
import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMultiplierKernelBoundExact as MultiplierAbstract
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as OfficialLuo

record NatToRationalOrderEmbedding : Set₁ where
  field
    embed : Nat → ℚ

    embedNonnegative :
      (value : Nat) → ℚBase._≤_ 0ℚ (embed value)

    embedMonotone :
      {left right : Nat} →
      ℕ._≤_ left right →
      ℚBase._≤_ (embed left) (embed right)

open NatToRationalOrderEmbedding public

record ResidueGapHardWindowIdentification
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time) : Setω where
  field
    natEmbedding : NatToRationalOrderEmbedding

    cutoffControlAt :
      (shell : Nat) → Cutoff.LuoCutoffLocalizedMajorant shell

    residueGapAuthority : Gap.ExactResidueScaleOperatorGapAuthority
    residueGapAuthorityMeaning :
      residueGapAuthority ≡ Gap.exactResidueScaleOperatorGapAuthority

    ForcedTailOutputsAreProducedByResidueGap : Set
    forcedTailOutputsAreProducedByResidueGap :
      ForcedTailOutputsAreProducedByResidueGap

    PhysicalPairKernelEqualsCertifiedPairKernel : Set
    physicalPairKernelEqualsCertifiedPairKernel :
      PhysicalPairKernelEqualsCertifiedPairKernel

    hardIntegralMeaning :
      (shell : Nat) →
      MultiplierAbstract.hardTerminalWindowIntegral
        (Multiplier.canonicalLuoMultiplierAuthority
          (PreBudget.multiplierRealization data))
        shell (PreBudget.solution data)
      ≡
      embed natEmbedding
        (Cutoff.localizedLowFrequencyGradientIntegral
          (cutoffControlAt shell))

    hardBudgetAt : Nat → ℚ
    hardBudgetMeaning :
      (shell : Nat) →
      hardBudgetAt shell
      ≡ embed natEmbedding
          (Cutoff.bkmThreshold (cutoffControlAt shell))

    universalDeltaNonnegative :
      ℚBase._≤_ 0ℚ
        (OfficialLuo.universalDeltaBKM
          (PreBudget.sourceCarrier data))

    scaledBudgetBelowLuoDelta :
      (shell : Nat) →
      ℚBase._≤_
        (ℚBase._*_
          (MultiplierAbstract.hardSmoothMultiplierLInfinityConstant
            (Multiplier.canonicalLuoMultiplierAuthority
              (PreBudget.multiplierRealization data)))
          (hardBudgetAt shell))
        (OfficialLuo.universalDeltaBKM
          (PreBudget.sourceCarrier data))

open ResidueGapHardWindowIdentification public

hardBudgetNonnegativeFromIdentification :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (identification : ResidueGapHardWindowIdentification data) →
  (shell : Nat) →
  ℚBase._≤_ 0ℚ (hardBudgetAt identification shell)
hardBudgetNonnegativeFromIdentification identification shell
  rewrite hardBudgetMeaning identification shell =
  embedNonnegative
    (natEmbedding identification)
    (Cutoff.bkmThreshold (cutoffControlAt identification shell))

hardIntegralBelowBudgetFromResidueGap :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (identification : ResidueGapHardWindowIdentification data) →
  (shell : Nat) →
  ℚBase._≤_
    (MultiplierAbstract.hardTerminalWindowIntegral
      (Multiplier.canonicalLuoMultiplierAuthority
        (PreBudget.multiplierRealization data))
      shell (PreBudget.solution data))
    (hardBudgetAt identification shell)
hardIntegralBelowBudgetFromResidueGap identification shell
  rewrite hardIntegralMeaning identification shell
        | hardBudgetMeaning identification shell =
  embedMonotone
    (natEmbedding identification)
    (Cutoff.luoLocalizedQuantityBelowThreshold
      shell (cutoffControlAt identification shell))

residueGapDerivedTerminalBudgetFamily :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  ResidueGapHardWindowIdentification data →
  PreBudget.DerivedLuoTerminalBudgetFamily data
residueGapDerivedTerminalBudgetFamily identification = record
  { hardBudgetAt = hardBudgetAt identification
  ; hardBudgetNonnegative =
      hardBudgetNonnegativeFromIdentification identification
  ; universalDeltaNonnegative =
      universalDeltaNonnegative identification
  ; hardIntegralBelowBudget =
      hardIntegralBelowBudgetFromResidueGap identification
  ; scaledBudgetBelowLuoDelta =
      scaledBudgetBelowLuoDelta identification
  }

residueGapBudgetAlgebraClosed : Bool
residueGapBudgetAlgebraClosed = true

physicalPairKernelIdentificationStillRequired : Bool
physicalPairKernelIdentificationStillRequired = true

residueGapBudgetAlgebraClosedIsTrue :
  residueGapBudgetAlgebraClosed ≡ true
residueGapBudgetAlgebraClosedIsTrue = refl

physicalPairKernelIdentificationStillRequiredIsTrue :
  physicalPairKernelIdentificationStillRequired ≡ true
physicalPairKernelIdentificationStillRequiredIsTrue = refl
