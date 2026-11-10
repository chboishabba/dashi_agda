module DASHI.Physics.YangMills.YMClayE1A3OriginalR445CrossCutoffSourceExact where

------------------------------------------------------------------------
-- SOURCE-FIRST E1 / A3: actual original Wilson 3 -> 1 blocked
-- expectation and its bare-coarse comparison.
--
-- THIS DOES NOT ASSUME the false identity:
--    effective blocked Wilson measure = bare coarse Wilson measure.
--
-- At fine size (suc 3) = 4 and coarse size (suc 1) = 2,
-- the fine R445 pushforward and the E1 changing-cutoff original Wilson
-- expectation use *definitionally the same* genuine Wilson Gibbs/Haar
-- measure, beta(3), and native two-link SU(N) blocking map.
--
-- The only unconditional cross-cutoff equality is with the EFFECTIVE
-- pushed-forward coarse functional. The bare coarse Wilson functional
-- at beta(1) is separately selected; comparison remains the physical
-- RG matching obligation for all nonconstant tests.
--
-- The constant unit test provides a real, source-backed consistency
-- base case using original Haar normalization and positive partition.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _<ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayE1OriginalSUNDependentCylinderExact as E1
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  -- This is the ORIGINAL coarse 2^4-lattice observable carrier,
  -- NOT the effective probability law.
  CoarseTest : Set
  CoarseTest = Push.CoarseLinks
    theory traceData exponential (beta 3) oneLink bilateral divide → ℝ

  originalFineBlockPullbackCylinder : CoarseTest →
    E1.Cylinder theory traceData exponential beta oneLink bilateral divide
  originalFineBlockPullbackCylinder observable 3 links =
    observable (Push.actualBlockedLinkMap
      theory traceData exponential (beta 3) oneLink bilateral divide
      links)
  originalFineBlockPullbackCylinder observable _ _ = 0ℝ

  originalBareCoarseCylinder : CoarseTest →
    E1.Cylinder theory traceData exponential beta oneLink bilateral divide
  originalBareCoarseCylinder observable 1 links = observable links
  originalBareCoarseCylinder observable _ _ = 0ℝ

  originalR445EffectiveCoarseExpectation : CoarseTest → ℝ
  originalR445EffectiveCoarseExpectation observable =
    Push.actualPushforwardNormalized
      theory traceData exponential (beta 3) oneLink bilateral divide
      observable

  originalE1FineBlockedExpectation : CoarseTest → ℝ
  originalE1FineBlockedExpectation observable =
    E1.actualOriginalWilsonCylinderExpectation
      theory traceData exponential beta oneLink bilateral divide
      3 (originalFineBlockPullbackCylinder observable)

  originalE1BareCoarseExpectation : CoarseTest → ℝ
  originalE1BareCoarseExpectation observable =
    E1.actualOriginalWilsonCylinderExpectation
      theory traceData exponential beta oneLink bilateral divide
      1 (originalBareCoarseCylinder observable)

  -- The FULL fine interacting measure is literally the original E1
  -- cutoff-3 measure; this holds on arbitrary coarse tests.
  originalE1FineBlockedIsR445EffectiveCoarse :
    (observable : CoarseTest) →
    originalE1FineBlockedExpectation observable
    ≡ originalR445EffectiveCoarseExpectation observable
  originalE1FineBlockedIsR445EffectiveCoarse observable = refl

  -- The coarse cylinder at n=1 is the genuine independently selected
  -- original bare Wilson measure with beta(1).
  originalE1CoarseIsBareWilson :
    (observable : CoarseTest) →
    originalE1BareCoarseExpectation observable
    ≡
    E1.actualOriginalWilsonCylinderExpectation
      theory traceData exponential beta oneLink bilateral divide
      1 (λ _ links → observable links)
  originalE1CoarseIsBareWilson observable = refl

  -- The unit case of matching the genuine R445 effective coarse state
  -- to the genuine bare Wilson state is now proved from original Haar
  -- integration, without identifying the two probability laws.
  originalR445UnitEqualsOriginalBareCoarseUnit :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (divideSelf : ∀ denominator →
      0ℝ <ℝ denominator → divide denominator denominator ≡ 1ℝ) →
    originalR445EffectiveCoarseExpectation (λ _ → 1ℝ)
      ≡ originalE1BareCoarseExpectation (λ _ → 1ℝ)
  originalR445UnitEqualsOriginalBareCoarseUnit
    ordered strictToWeak strict divideSelf =
    trans
      (Push.actualPushforwardUnitNormalized
        theory traceData exponential (beta 3) oneLink bilateral divide
        ordered strictToWeak strict divideSelf)
      (sym
        (E1.originalWilsonUnitCylinderExpectationIsOne
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak strict divideSelf 1))

  -- Unpaid true cross-cutoff original Wilson RG theorem: for a chosen
  -- nonconstant coarse Wilson word W, bound or identify
  --
  --   originalR445EffectiveCoarseExpectation W
  --       versus originalE1BareCoarseExpectation W.
  --
  -- In general the effective blocked action contains extra operators
  -- and does NOT coincide with a Wilson plaquette action at beta(1).
