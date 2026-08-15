module DASHI.Physics.YangMills.BalabanCMP122Equation1100EntropyBudgetExact where

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
-- Roman Kotecky and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- DASHI CONTRIBUTION
--
-- Turn the literal CMP122 equation-(1.100) suppression factor into the actual
-- shell amplitude consumed by the checked Gate-4 shared-slack theorem.
--
-- Reserve part of the source diameter decay to pay the polymer norm weight.
-- Let r_n be the residual decay after this weight cancellation.  If
--
--   ||R_k(X)||_weighted <= exp(-p0(g_k)) r_n
--
-- for every X in the rooted shell S_n, and the SAME shell geometry satisfies
--
--   |S_n| r_n <= 2^{-n},
--
-- then finite shell summation gives
--
--   sum_{X in S_n} ||R_k(X)||_weighted
--      <= exp(-p0(g_k)) 2^{-n}.
--
-- Therefore the shared-slack amplitude is not an unspecified a_k on this
-- route: it is exactly the source small factor exp(-p0(g_k)).  The remaining
-- source/repository seam is only the weight split and the rooted entropy bound
-- using the same d_k geometry.  CMP119 (2.31) explicitly permits an arbitrarily
-- large R-decay constant, so there is source-level room to reserve decay for
-- both purposes.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP122Equation1100DirectExact as Source
import DASHI.Physics.YangMills.BalabanYM4ROperationEntropyShellExact as Shell
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record Equation1100RootedEntropyData
    (Scale Volume Root Polymer Boundary : Set) : Set₁ where
  field
    source : Source.CMP122Equation1100Pointwise Scale Polymer Boundary

    shellPolymers : Scale → Volume → Root → Nat → List Polymer
    boundaryAt : Scale → Volume → Root → Boundary

    -- The exact norm used by the combined one-step polymer coordinate.
    weightedRNorm : Scale → Volume → Root → Polymer → ℚ

    -- Residual source decay after paying the repository norm weight.
    residualDecay : Scale → Volume → Root → Nat → ℚ

    suppressionNonnegative : ∀ scale →
      0ℚ ≤ Source.p0Suppression source scale

    -- Literal equation (1.100), after identifying the repository R expression
    -- and splitting its exp(-kappa d_k(X)) between norm weight and reserve.
    equation1100AfterWeightSplit :
      ∀ scale volume root depth polymer →
      polymer Shell.∈ shellPolymers scale volume root depth →
      weightedRNorm scale volume root polymer
      ≤ Source.p0Suppression source scale
        * residualDecay scale volume root depth

    -- Rooted animal entropy paid from the residual source decay.  This is the
    -- precise same-geometry theorem required from P06/CMP119 rather than an
    -- independently normalized counting estimate.
    entropyConsumesResidualDecay : ∀ scale volume root depth →
      Shell.natAsRational (length (shellPolymers scale volume root depth))
        * residualDecay scale volume root depth
      ≤ Geo.halfPower depth

open Equation1100RootedEntropyData public

entropyTimesEquation1100Envelope :
  ∀ {Scale Volume Root Polymer Boundary}
    (dataSet : Equation1100RootedEntropyData
      Scale Volume Root Polymer Boundary)
    scale volume root depth →
  Shell.natAsRational
      (length (shellPolymers dataSet scale volume root depth))
    * (Source.p0Suppression (source dataSet) scale
      * residualDecay dataSet scale volume root depth)
  ≤ LF.scaledShellMajorant
      (Source.p0Suppression (source dataSet) scale) depth
entropyTimesEquation1100Envelope dataSet scale volume root depth =
  let
    count = Shell.natAsRational
      (length (shellPolymers dataSet scale volume root depth))
    p0 = Source.p0Suppression (source dataSet) scale
    residual = residualDecay dataSet scale volume root depth

    scaled :
      p0 * (count * residual) ≤ p0 * Geo.halfPower depth
    scaled = Norm.scaleNonnegative p0
      (suppressionNonnegative dataSet scale)
      (entropyConsumesResidualDecay dataSet scale volume root depth)

    rearrangeLeft : count * (p0 * residual) ≡ p0 * (count * residual)
    rearrangeLeft = ℚRing.solve-∀ count p0 residual
  in
  subst
    (λ lower → lower ≤ p0 * Geo.halfPower depth)
    (sym rearrangeLeft)
    scaled
  where
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

cmp122Equation1100RootedShell :
  ∀ {Scale Volume Root Polymer Boundary} →
  Equation1100RootedEntropyData Scale Volume Root Polymer Boundary →
  Shell.ROperationRootedEntropyShell Scale Volume Root Polymer
cmp122Equation1100RootedShell dataSet = record
  { Shell.ROperationRootedEntropyShell.shellPolymers = shellPolymers dataSet
  ; Shell.ROperationRootedEntropyShell.weightedRNorm = weightedRNorm dataSet
  ; Shell.ROperationRootedEntropyShell.pointwiseEnvelope =
      λ scale volume root depth →
        Source.p0Suppression (source dataSet) scale
          * residualDecay dataSet scale volume root depth
  ; Shell.ROperationRootedEntropyShell.shellAmplitude =
      Source.p0Suppression (source dataSet)
  ; Shell.ROperationRootedEntropyShell.pointwiseROperationDecay =
      equation1100AfterWeightSplit dataSet
  ; Shell.ROperationRootedEntropyShell.entropyTimesPointwiseFitsGeometric =
      entropyTimesEquation1100Envelope dataSet
  }

cmp122Equation1100ShellAmplitudeExact :
  ∀ {Scale Volume Root Polymer Boundary}
    (dataSet : Equation1100RootedEntropyData
      Scale Volume Root Polymer Boundary)
    scale volume root depth →
  Shell.rootedRActivityShell
      (cmp122Equation1100RootedShell dataSet)
      scale volume root depth
  ≤ LF.scaledShellMajorant
      (Source.p0Suppression (source dataSet) scale) depth
cmp122Equation1100ShellAmplitudeExact dataSet =
  Shell.rootedRActivityShellBelowGeometric
    (cmp122Equation1100RootedShell dataSet)

cmp122Equation1100EntropyAssemblyLevel : ProofLevel
cmp122Equation1100EntropyAssemblyLevel = machineChecked

-- These are now the only two physical leaves in the pointwise->shell segment.
cmp122Equation1100WeightSplitIdentificationLevel : ProofLevel
cmp122Equation1100WeightSplitIdentificationLevel = conditional

cmp119RootedEntropyConsumesResidualDecayLevel : ProofLevel
cmp119RootedEntropyConsumesResidualDecayLevel = conditional
