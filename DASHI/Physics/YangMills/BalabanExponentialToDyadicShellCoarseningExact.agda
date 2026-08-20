module DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact where

------------------------------------------------------------------------
-- ROUND71: SOURCE EXPONENTIAL LOCALISATION -> DYADIC UNIFIED-NORM SHELL
--
-- PRIMARY SOURCES / CALIBRATION
--
-- IMPORTANT CMP 99 DISAMBIGUATION
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
-- Theorem 3.14 / equation (3.154): background-propagator domain-sequence
-- comparison with the additional marked distance-to-discrepancy decay used
-- below.  THIS is the CMP 99 paper used by the marked random-walk argument.
--
-- Do not confuse it with the distinct paper in the same volume:
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99(1) (1985),
-- 75--102. DOI: 10.1007/BF01466594.
-- That paper supplies the regular gauge chart/gauge-fixing input, not the
-- Theorem 3.14/(3.154) marked propagator comparison.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Equations (1.26), (1.29), Lemma 3 / (2.38): residual localization/tree
-- summability with a still-positive exponential rate.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
-- Section 5 derives exponential decay of the differentiated polarization
-- kernel after the localization sum.
--
-- Earlier propagator lineage used by the same carrier:
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01215753.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- The source gives exponential localization; the unified norm currently uses
-- the convenient dyadic shell (1/2)^d.  These are not different physical
-- estimates.  Once one coarse shell width has been chosen so that the source
-- per-shell decay factor q satisfies
--
--       0 <= q <= 1/2,
--
-- induction gives
--
--       q^d <= (1/2)^d
--
-- for every shell depth.  Thus the remaining standard-analysis step is only
-- to choose/certify a shell width R with exp(-delta R) <= 1/2 for the positive
-- source localization rate delta.  No new Yang--Mills decay theorem is needed
-- after that source-native rate has been instantiated.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as KP
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

rationalPower : ℚ → Nat → ℚ
rationalPower base zero = 1ℚ
rationalPower base (suc n) = rationalPower base n * base

powerNonnegative : ∀ base →
  0ℚ ≤ base →
  ∀ n → 0ℚ ≤ rationalPower base n
powerNonnegative base baseNonnegative zero = ℚP.0≤1
powerNonnegative base baseNonnegative (suc n) =
  let
    instance
      powerInstance : NonNegative (rationalPower base n)
      powerInstance = nonNegative (powerNonnegative base baseNonnegative n)
      baseInstance : NonNegative base
      baseInstance = nonNegative baseNonnegative
      productInstance : NonNegative (rationalPower base n * base)
      productInstance = ℚP.nonNeg*nonNeg⇒nonNeg (rationalPower base n) base
  in
  ℚP.nonNegative⁻¹ (rationalPower base n * base)

record DyadicCoarseningCriterion : Set where
  field
    sourcePerShellDecay : ℚ
    sourceDecayNonnegative : 0ℚ ≤ sourcePerShellDecay
    sourceDecayAtMostHalf : sourcePerShellDecay ≤ KP.half

open DyadicCoarseningCriterion public

sourcePowerBelowDyadicPower :
  (criterion : DyadicCoarseningCriterion) →
  ∀ depth →
  rationalPower (sourcePerShellDecay criterion) depth
  ≤ KP.halfPower depth
sourcePowerBelowDyadicPower criterion zero = ℚP.≤-refl
sourcePowerBelowDyadicPower criterion (suc depth) =
  let
    induction = sourcePowerBelowDyadicPower criterion depth
    leftNonnegative = powerNonnegative
      (sourcePerShellDecay criterion)
      (sourceDecayNonnegative criterion)
      depth
    halfNonnegative = KP.halfPowerNonnegative depth
  in
  ℚP.*-mono-≤
    leftNonnegative
    induction
    (sourceDecayNonnegative criterion)
    (sourceDecayAtMostHalf criterion)

record SourceExponentialShellMajorant : Set₁ where
  field
    criterion : DyadicCoarseningCriterion
    shellValue : Nat → ℚ
    amplitude : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude

    sourceExponentialShellBound : ∀ depth →
      shellValue depth
      ≤ amplitude * rationalPower
          (sourcePerShellDecay criterion) depth

open SourceExponentialShellMajorant public

sourceExponentialShellIsDyadic :
  (dataSet : SourceExponentialShellMajorant) →
  ∀ depth →
  shellValue dataSet depth
  ≤ amplitude dataSet * KP.halfPower depth
sourceExponentialShellIsDyadic dataSet depth =
  ℚP.≤-trans
    (sourceExponentialShellBound dataSet depth)
    (Norm.scaleNonnegative
      (amplitude dataSet)
      (amplitudeNonnegative dataSet)
      (sourcePowerBelowDyadicPower (criterion dataSet) depth))

exponentialToDyadicShellCompilerLevel : ProofLevel
exponentialToDyadicShellCompilerLevel = machineChecked

-- Source/standard-analysis seam only: for the positive background-propagator
-- CMP 99(3) / CMP 109 / CMP 116 localization exponent delta, choose a coarse
-- shell width R and certify the numerical inequality exp(-delta R) <= 1/2 in
-- the source normalization.  Once that one scalar inequality is available,
-- every shell-depth comparison above is exact downstream algebra.
physicalSourceExponentialRateToHalfLevel : ProofLevel
physicalSourceExponentialRateToHalfLevel = conditional
