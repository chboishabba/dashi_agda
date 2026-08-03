module DASHI.Physics.YangMills.BalabanP11UniformAbsorptionReductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987).
-- DOI: 10.1007/BF01215223.
--
-- The source-scale absorption inequality is not assumed here.  The module
-- reduces it to two explicit scalar facts: a uniform lower bound p0Minimum
-- for p0(k), and payment of the entropy threshold at that minimum.  Ordered
-- multiplication and transitivity then construct the scale-indexed P11
-- witness consumed by Step V.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _+ℝ_
  ; _*ℝ_
  ; _-ℝ_
  ; 0ℝ
  ; 1ℝ
  )
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( dashi-internal-proof
  ; provedConditionalReducer
  )
open import DASHI.Physics.YangMills.CompactLieProofLevel

p11EntropyThreshold : ℝ
p11EntropyThreshold =
  ((LargeField.d-dim -ℝ 1ℝ) *ℝ LargeField.logℝ LargeField.L-constant)
  +ℝ LargeField.C-abs-const

record P11UniformAbsorptionInputs : Set₁ where
  field
    p0Minimum : ℝ

    p0MinimumNonnegative :
      0ℝ ≤ℝ p0Minimum

    cAbsNonnegative :
      0ℝ ≤ℝ LargeField.c-abs

    entropyThresholdPaidAtMinimum :
      p11EntropyThreshold ≤ℝ
        (LargeField.c-abs *ℝ p0Minimum)

    p0MinimumBelowEveryScale :
      ∀ (scale : ℕ) →
      p0Minimum ≤ℝ LargeField.p0 scale

open P11UniformAbsorptionInputs public

p11AbsorptionAtScale :
  P11UniformAbsorptionInputs →
  ∀ (scale : ℕ) →
  p11EntropyThreshold ≤ℝ
    (LargeField.c-abs *ℝ LargeField.p0 scale)
p11AbsorptionAtScale inputs scale =
  LargeField.OrderedRealKernel.≤-trans
    LargeField.currentOrderedRealKernel
    p11EntropyThreshold
    (LargeField.c-abs *ℝ p0Minimum inputs)
    (LargeField.c-abs *ℝ LargeField.p0 scale)
    (entropyThresholdPaidAtMinimum inputs)
    (LargeField.OrderedRealKernel.*-mono-≤-nonneg
      LargeField.currentOrderedRealKernel
      LargeField.c-abs
      LargeField.c-abs
      (p0Minimum inputs)
      (LargeField.p0 scale)
      (cAbsNonnegative inputs)
      (p0MinimumNonnegative inputs)
      (LargeField.OrderedRealKernel.≤-refl
        LargeField.currentOrderedRealKernel
        LargeField.c-abs)
      (p0MinimumBelowEveryScale inputs scale))

p11AbsorptionConditionFromUniformMinimum :
  P11UniformAbsorptionInputs →
  LargeField.ImportedAbsorptionCondition
p11AbsorptionConditionFromUniformMinimum inputs = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanP11UniformAbsorptionReductionExact.p11AbsorptionAtScale; source normalization follows Balaban CMP 109, DOI 10.1007/BF01215223"
  ; status = provedConditionalReducer
  ; absorptionInequality = p11AbsorptionAtScale inputs
  }

record P11UniformAbsorptionDischargePackage : Set₁ where
  field
    inputs : P11UniformAbsorptionInputs
    condition : LargeField.ImportedAbsorptionCondition
    conditionIsCanonical :
      condition ≡ p11AbsorptionConditionFromUniformMinimum inputs

open P11UniformAbsorptionDischargePackage public

p11UniformAbsorptionReductionLevel : ProofLevel
p11UniformAbsorptionReductionLevel = machineChecked

p11UniformAbsorptionPhysicalInputsLevel : ProofLevel
p11UniformAbsorptionPhysicalInputsLevel = conditional
