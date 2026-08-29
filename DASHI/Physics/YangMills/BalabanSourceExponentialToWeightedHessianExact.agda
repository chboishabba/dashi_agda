module DASHI.Physics.YangMills.BalabanSourceExponentialToWeightedHessianExact where

------------------------------------------------------------------------
-- ROUND71: SOURCE EXPONENTIAL HESSIAN TAIL -> WEIGHTED QUASI-LOCAL ROW
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
-- The marked domain-sequence comparison used here is Theorem 3.14 / (3.154)
-- of THIS background-propagator paper, not the distinct CMP 99(1)
-- gauge-fixing paper DOI 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- DASHI CONTRIBUTION
--
-- The mass-gap route does not need to route the source exponential Hessian
-- tail through the rooted KP activity before obtaining quasi-local influence.
-- If
--
--     h_d <= A q^d,       0 <= q <= 1/2,
--
-- then the existing exponential->dyadic compiler gives
--
--     h_d <= A (1/2)^d.
--
-- Weighting by (3/2)^d gives
--
--     (3/2)^d h_d <= A (3/4)^d,
--
-- and every finite partial row obeys
--
--     sum_{d<n} (3/2)^d h_d <= 4 A.
--
-- This is volume-independent.  KP remains valuable for the stronger
-- same-coordinate statement `h_d <= c_H rootedShell_d`, but it is not a
-- logically necessary intermediate for source exponential decay -> weighted
-- propagation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact as Dyadic
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Weighted
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record SourceWeightedHessianData : Set₁ where
  field
    exponentialShell : Dyadic.SourceExponentialShellMajorant

open SourceWeightedHessianData public

sourceWeightedShell : SourceWeightedHessianData → Nat → ℚ
sourceWeightedShell dataSet depth =
  Weighted.threeHalvesPower depth
  * Dyadic.shellValue (exponentialShell dataSet) depth

sourceWeightedPartial : SourceWeightedHessianData → Nat → ℚ
sourceWeightedPartial dataSet zero = 0ℚ
sourceWeightedPartial dataSet (suc depth) =
  sourceWeightedPartial dataSet depth
  + sourceWeightedShell dataSet depth

sourceWeightedShellBelowThreeQuarter :
  (dataSet : SourceWeightedHessianData) →
  ∀ depth →
  sourceWeightedShell dataSet depth
  ≤ Dyadic.amplitude (exponentialShell dataSet)
      * Weighted.threeQuartersPower depth
sourceWeightedShellBelowThreeQuarter dataSet depth =
  let
    source = exponentialShell dataSet
    dyadic = Dyadic.sourceExponentialShellIsDyadic source depth
    weighted = Norm.scaleNonnegative
      (Weighted.threeHalvesPower depth)
      (Weighted.threeHalvesPowerNonnegative depth)
      dyadic
  in
  subst
    (λ upper → sourceWeightedShell dataSet depth ≤ upper)
    (weightedIdentity (Dyadic.amplitude source) depth)
    weighted
  where
  weightedIdentity : ∀ amplitude depth →
    Weighted.threeHalvesPower depth
      * (amplitude * StepV.halfPower depth)
    ≡ amplitude * Weighted.threeQuartersPower depth
  weightedIdentity amplitude depth
    rewrite Weighted.halfThreeHalvesPowerIsThreeQuartersPower depth =
    ℚRing.solve []

sourceWeightedPartialBelowThreeQuarterSum :
  (dataSet : SourceWeightedHessianData) →
  ∀ depth →
  sourceWeightedPartial dataSet depth
  ≤ Dyadic.amplitude (exponentialShell dataSet)
      * Weighted.threeQuarterPartialSum depth
sourceWeightedPartialBelowThreeQuarterSum dataSet zero =
  subst
    (λ right → 0ℚ ≤ right)
    (ℚRing.solve-∀ (Dyadic.amplitude (exponentialShell dataSet)))
    ℚP.≤-refl
sourceWeightedPartialBelowThreeQuarterSum dataSet (suc depth) =
  let
    previous = sourceWeightedPartialBelowThreeQuarterSum dataSet depth
    shell = sourceWeightedShellBelowThreeQuarter dataSet depth
    added = ℚP.+-mono-≤ previous shell
  in
  subst
    (λ upper → sourceWeightedPartial dataSet (suc depth) ≤ upper)
    (ℚRing.solve-∀
      (Dyadic.amplitude (exponentialShell dataSet))
      (Weighted.threeQuarterPartialSum depth)
      (Weighted.threeQuartersPower depth))
    added

four : ℚ
four = + 4 / 1

fourNonnegative : 0ℚ ≤ four
fourNonnegative =
  let
    instance
      selected : NonNegative four
      selected = ℚP.normalize-nonNeg 4 1
  in
  ℚP.nonNegative⁻¹ four

sourceWeightedPartialBelowFourAmplitude :
  (dataSet : SourceWeightedHessianData) →
  ∀ depth →
  sourceWeightedPartial dataSet depth
  ≤ four * Dyadic.amplitude (exponentialShell dataSet)
sourceWeightedPartialBelowFourAmplitude dataSet depth =
  let
    source = exponentialShell dataSet
    partial = sourceWeightedPartialBelowThreeQuarterSum dataSet depth
    quarterBound = Weighted.quarterPartialBelowOne depth
    amplitudeNonnegative = Dyadic.amplitudeNonnegative source

    scaledByAmplitude = Norm.scaleNonnegative
      (Dyadic.amplitude source)
      amplitudeNonnegative
      quarterBound

    scaledByFour = Norm.scaleNonnegative
      four
      fourNonnegative
      scaledByAmplitude

    normalizedScaledByFour :
      Dyadic.amplitude source * Weighted.threeQuarterPartialSum depth
      ≤ four * Dyadic.amplitude source
    normalizedScaledByFour =
      subst
        (λ left → left ≤ four * Dyadic.amplitude source)
        (ℚRing.solve-∀
          (Dyadic.amplitude source)
          (Weighted.threeQuarterPartialSum depth))
        scaledByFour
  in
  ℚP.≤-trans partial normalizedScaledByFour

sourceExponentialToWeightedHessianLevel : ProofLevel
sourceExponentialToWeightedHessianLevel = machineChecked

-- Physical seam: instantiate `exponentialShell` with the SAME twice-
-- differentiated CMP99(3)/109/116 marked activity entering the physical L7
-- effective action.  Once its amplitude and one coarse per-shell factor
-- q <= 1/2 are certified, the weighted row bound above is exact.
physicalMarkedActivityInstantiatesSourceWeightedHessianLevel : ProofLevel
physicalMarkedActivityInstantiatesSourceWeightedHessianLevel = conditional
