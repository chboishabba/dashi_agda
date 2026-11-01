module DASHI.Physics.YangMills.BalabanCMP122Equation1100SharedSlackExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Complete the source-to-budget arithmetic once equation (1.100) has been
-- put in the repository's weighted rooted-shell geometry.
--
-- The previous module proves
--
--   shell_n <= exp(-p0(g_k)) 2^{-n}.
--
-- Hence the finite large-field contribution is bounded by
--
--   2 exp(-p0(g_k)).
--
-- This module makes that source factor the literal amplitude in the checked
-- Gate-4 shared-slack theorem.  The numerical one-step condition is therefore
-- exactly
--
--   E_pert,k + 2 exp(-p0(g_k)) <= (1-q_k) K_max.
--
-- No free a_k remains after the CMP122 identification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP122Equation1100DirectExact as Source
import DASHI.Physics.YangMills.BalabanCMP122Equation1100EntropyBudgetExact as Entropy
import DASHI.Physics.YangMills.BalabanYM4ROperationEntropyShellExact as Shell
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

rootedRPartial :
  ∀ {Scale Volume Root Polymer Boundary} →
  Entropy.Equation1100RootedEntropyData Scale Volume Root Polymer Boundary →
  Scale → Volume → Root → Nat → ℚ
rootedRPartial dataSet scale volume root zero = 0ℚ
rootedRPartial dataSet scale volume root (suc depth) =
  rootedRPartial dataSet scale volume root depth
  + Shell.rootedRActivityShell
      (Entropy.cmp122Equation1100RootedShell dataSet)
      scale volume root depth

record Equation1100LargeFieldContribution
    (Scale Volume Root Polymer Boundary : Set) : Set₁ where
  field
    entropyData :
      Entropy.Equation1100RootedEntropyData Scale Volume Root Polymer Boundary

    largeFieldContribution : Scale → Volume → Root → Nat → ℚ

    contributionBelowRootedPartial : ∀ scale volume root cutoff →
      largeFieldContribution scale volume root cutoff
      ≤ rootedRPartial entropyData scale volume root cutoff

open Equation1100LargeFieldContribution public

rootedPartialBelowSourceMajorant :
  ∀ {Scale Volume Root Polymer Boundary}
    (dataSet : Equation1100LargeFieldContribution
      Scale Volume Root Polymer Boundary)
    scale volume root cutoff →
  rootedRPartial (entropyData dataSet) scale volume root cutoff
  ≤ LF.scaledShellPartial
      (Source.p0Suppression
        (Entropy.source (entropyData dataSet)) scale)
      cutoff
rootedPartialBelowSourceMajorant dataSet scale volume root zero =
  ℚP.≤-refl
rootedPartialBelowSourceMajorant dataSet scale volume root (suc depth) =
  ℚP.+-mono-≤
    (rootedPartialBelowSourceMajorant dataSet scale volume root depth)
    (Entropy.cmp122Equation1100ShellAmplitudeExact
      (entropyData dataSet) scale volume root depth)

cmp122LargeFieldContributionBelowTwiceSuppression :
  ∀ {Scale Volume Root Polymer Boundary}
    (dataSet : Equation1100LargeFieldContribution
      Scale Volume Root Polymer Boundary)
    scale volume root cutoff →
  largeFieldContribution dataSet scale volume root cutoff
  ≤ Source.p0Suppression (Entropy.source (entropyData dataSet)) scale
      * Geo.twoℚ
cmp122LargeFieldContributionBelowTwiceSuppression dataSet scale volume root cutoff =
  ℚP.≤-trans
    (contributionBelowRootedPartial dataSet scale volume root cutoff)
    (ℚP.≤-trans
      (rootedPartialBelowSourceMajorant dataSet scale volume root cutoff)
      (LF.scaledShellPartialBelowTwiceAmplitude
        (Source.p0Suppression (Entropy.source (entropyData dataSet)) scale)
        cutoff
        (Entropy.suppressionNonnegative (entropyData dataSet) scale)))

record Equation1100SharedSlackAtStep
    (Scale Volume Root Polymer Boundary : Set) : Set₁ where
  field
    largeField :
      Equation1100LargeFieldContribution Scale Volume Root Polymer Boundary
    scale : Scale

    contraction perturbativeError smallFieldCap : ℚ

    sourceSharedSlack :
      perturbativeError
        + Source.p0Suppression
            (Entropy.source (entropyData largeField)) scale * Geo.twoℚ
      ≤ (1ℚ - contraction) * smallFieldCap

open Equation1100SharedSlackAtStep public

cmp122SourceSharedSlack :
  ∀ {Scale Volume Root Polymer Boundary} →
  Equation1100SharedSlackAtStep Scale Volume Root Polymer Boundary →
  LF.SharedPolymerSlackAtStep
cmp122SourceSharedSlack dataSet = record
  { LF.SharedPolymerSlackAtStep.contraction = contraction dataSet
  ; LF.SharedPolymerSlackAtStep.perturbativeError = perturbativeError dataSet
  ; LF.SharedPolymerSlackAtStep.smallFieldCap = smallFieldCap dataSet
  ; LF.SharedPolymerSlackAtStep.largeFieldAmplitude =
      Source.p0Suppression
        (Entropy.source (entropyData (largeField dataSet)))
        (scale dataSet)
  ; LF.SharedPolymerSlackAtStep.slack =
      (1ℚ - contraction dataSet) * smallFieldCap dataSet
  ; LF.SharedPolymerSlackAtStep.slackDefinition = refl
  ; LF.SharedPolymerSlackAtStep.perturbativePlusLargeFieldFits =
      sourceSharedSlack dataSet
  }

cmp122Equation1100FiniteContributionLevel : ProofLevel
cmp122Equation1100FiniteContributionLevel = machineChecked

cmp122Equation1100SharedSlackAssemblyLevel : ProofLevel
cmp122Equation1100SharedSlackAssemblyLevel = machineChecked

cmp122CombinedNormContributionIdentificationLevel : ProofLevel
cmp122CombinedNormContributionIdentificationLevel = conditional

cmp122NumericalSharedSlackLevel : ProofLevel
cmp122NumericalSharedSlackLevel = conditional
