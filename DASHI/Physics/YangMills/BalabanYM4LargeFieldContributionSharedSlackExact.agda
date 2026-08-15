module DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact where

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
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- DASHI CONTRIBUTION
--
-- Direct bridge from a rooted R-operation shell estimate to the shared error
-- budget consumed by the lightweight Gate-4 invariant region.  This avoids the
-- stronger, unnecessary requirement that the large-field error itself decay by
-- a fixed geometric ratio in the RG scale index.
--
-- At one RG step, if the weighted rooted shell at diameter depth n obeys
--
--      shell(n) <= a 2^{-n},
--
-- then every finite rooted contribution is <= 2a.  Thus the combined polymer
-- step has enough room whenever
--
--      perturbativeError + 2a <= (1-q) Kmax.
--
-- The remaining physical producer is therefore sharply local in scale: obtain
-- the amplitude a from Bałaban's boundary-uniform R^(k)(X) estimate and the
-- rooted polymer entropy count in the SAME norm as the one-step RG cutset.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

scaledShellMajorant : ℚ → Nat → ℚ
scaledShellMajorant amplitude depth = amplitude * Geo.halfPower depth

scaledShellPartial : ℚ → Nat → ℚ
scaledShellPartial amplitude zero = 0ℚ
scaledShellPartial amplitude (suc depth) =
  scaledShellPartial amplitude depth + scaledShellMajorant amplitude depth

scaledShellPartialIsAmplitudeTimesTrace : ∀ amplitude depth →
  scaledShellPartial amplitude depth
  ≡ amplitude * Geo.traceShellPartialSum depth
scaledShellPartialIsAmplitudeTimesTrace amplitude zero =
  ℚRing.solve-∀ amplitude
scaledShellPartialIsAmplitudeTimesTrace amplitude (suc depth)
  rewrite scaledShellPartialIsAmplitudeTimesTrace amplitude depth =
  ℚRing.solve-∀ amplitude (Geo.traceShellPartialSum depth) (Geo.halfPower depth)

scaledShellPartialBelowTwiceAmplitude : ∀ amplitude depth →
  0ℚ ≤ amplitude →
  scaledShellPartial amplitude depth ≤ amplitude * Geo.twoℚ
scaledShellPartialBelowTwiceAmplitude amplitude depth amplitudeNonnegative =
  let
    instance
      amplitudeNN : NonNegative amplitude
      amplitudeNN = nonNegative amplitudeNonnegative

    scaledTrace :
      amplitude * Geo.traceShellPartialSum depth
      ≤ amplitude * Geo.twoℚ
    scaledTrace =
      ℚP.*-monoˡ-≤-nonNeg amplitude
        (Geo.traceShellPartialSumBelowTwo depth)
  in
  subst
    (λ lower → lower ≤ amplitude * Geo.twoℚ)
    (sym (scaledShellPartialIsAmplitudeTimesTrace amplitude depth))
    scaledTrace

record PhysicalRootedLargeFieldContribution
    (Scale Volume Root : Set) : Set₁ where
  field
    shellAmplitude : Scale → ℚ
    rootedShell : Scale → Volume → Root → Nat → ℚ
    largeFieldContribution : Scale → Volume → Root → Nat → ℚ

    amplitudeNonnegative : ∀ scale → 0ℚ ≤ shellAmplitude scale

    shellBelowGeometric : ∀ scale volume root depth →
      rootedShell scale volume root depth
      ≤ scaledShellMajorant (shellAmplitude scale) depth

    rootedShellPartial : Scale → Volume → Root → Nat → ℚ
    rootedShellPartial scale volume root zero = 0ℚ
    rootedShellPartial scale volume root (suc depth) =
      rootedShellPartial scale volume root depth
      + rootedShell scale volume root depth

    partialMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper

    -- The concrete norm identification: the large-field term appearing in the
    -- combined one-step polymer norm is bounded by this finite rooted shell sum.
    contributionBelowRootedSum : ∀ scale volume root cutoff →
      largeFieldContribution scale volume root cutoff
      ≤ rootedShellPartial scale volume root cutoff

open PhysicalRootedLargeFieldContribution public

rootedSumBelowScaledGeometric :
  ∀ {Scale Volume Root}
    (physical : PhysicalRootedLargeFieldContribution Scale Volume Root)
    scale volume root cutoff →
  rootedShellPartial physical scale volume root cutoff
  ≤ scaledShellPartial (shellAmplitude physical scale) cutoff
rootedSumBelowScaledGeometric physical scale volume root zero =
  ℚP.≤-refl
rootedSumBelowScaledGeometric physical scale volume root (suc depth) =
  partialMonotone physical
    (rootedSumBelowScaledGeometric physical scale volume root depth)
    (shellBelowGeometric physical scale volume root depth)

physicalLargeFieldContributionBelowTwiceAmplitude :
  ∀ {Scale Volume Root}
    (physical : PhysicalRootedLargeFieldContribution Scale Volume Root)
    scale volume root cutoff →
  largeFieldContribution physical scale volume root cutoff
  ≤ shellAmplitude physical scale * Geo.twoℚ
physicalLargeFieldContributionBelowTwiceAmplitude physical scale volume root cutoff =
  ℚP.≤-trans
    (contributionBelowRootedSum physical scale volume root cutoff)
    (ℚP.≤-trans
      (rootedSumBelowScaledGeometric physical scale volume root cutoff)
      (scaledShellPartialBelowTwiceAmplitude
        (shellAmplitude physical scale) cutoff
        (amplitudeNonnegative physical scale)))

record SharedPolymerSlackAtStep : Set where
  field
    contraction perturbativeError smallFieldCap largeFieldAmplitude : ℚ
    slack : ℚ

    slackDefinition :
      slack ≡ (1ℚ - contraction) * smallFieldCap

    perturbativePlusLargeFieldFits :
      perturbativeError + largeFieldAmplitude * Geo.twoℚ ≤ slack

open SharedPolymerSlackAtStep public

combinedErrorFitsInvariantSlack :
  (budget : SharedPolymerSlackAtStep) →
  perturbativeError budget + largeFieldAmplitude budget * Geo.twoℚ
  ≤ (1ℚ - contraction budget) * smallFieldCap budget
combinedErrorFitsInvariantSlack budget =
  subst
    (λ upper →
      perturbativeError budget + largeFieldAmplitude budget * Geo.twoℚ ≤ upper)
    (slackDefinition budget)
    (perturbativePlusLargeFieldFits budget)

largeFieldRootedSummationLevel : ProofLevel
largeFieldRootedSummationLevel = machineChecked

largeFieldSharedSlackAssemblyLevel : ProofLevel
largeFieldSharedSlackAssemblyLevel = machineChecked

physicalROperationToRootedShellAmplitudeLevel : ProofLevel
physicalROperationToRootedShellAmplitudeLevel = conditional
