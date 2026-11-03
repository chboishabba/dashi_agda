module DASHI.Physics.YangMills.YMClaySUNSideFourBlockedFineHaarObservableExact where

------------------------------------------------------------------------
-- R445 selected real SU(N) FINITE BLOCK-PULLBACK integration theorem.
--
-- A non-Abelian coarse link on the original periodic side-two torus is
-- the ordered two-link holonomy of the original side-four SUN links.
-- This module pulls coarse Wilson/Gibbs observables back onto the
-- ACTUAL fine original side-four SU(N) Gibbs measure built in R443/R445.
--
-- The same finite physical measure / betaFine / original density / Haar
-- constructor is used, not a newly invented probability distribution.
-- Only the existing one-link Haar bilateral + product-Fubini assumptions
-- and same-carrier pointwise observable congruence are consumed.
--
-- Important: the expectation E_fine[F(block U)] is the pushforward
-- observable functional BY DEFINITION. It is NOT proved equal to a
-- coarse `exp(-betaCoarse * WilsonAction)` product-Haar law. Such an
-- equality generally requires an RG effective action with extra terms.
-- This module does not claim Haar existence on continuous SU(N), tightness,
-- Wilson measure disintegration, reflection positivity, or mass gap.
--
-- Provenance: Wilson, Bałaban, finite Haar/Fubini, original DASHI owners.
-- Source-written, exact Agda kernel / real postulate audit still pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base using (Vec)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact as Constructed
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGaugeHaarExact as GaugeHaar
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as SUNBlock
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedWilsonGaugeExact as WilsonBlock
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory 3

  CoarseLinks : Set
  CoarseLinks = Variable.SUNPeriodicLinks theory 1

  selectedFineMeasure : Physical.PhysicalFiniteYMMeasure FineLinks ℝ
  selectedFineMeasure =
    Constructed.actualPeriodicProductMeasure
      theory traceData exponential 3 betaFine
      oneLink bilateral divide

  selectedBlock : FineLinks → CoarseLinks
  selectedBlock = SUNBlock.nativeSUNBlockLinks
    {m = 1} {l = 1} theory

  record CoarsePointwiseObservable (observable : CoarseLinks → ℝ) : Set where
    field
      sameAtAllBonds : ∀ left right →
        Pointwise.VariableBondPointwise theory 1 left right →
        observable left ≡ observable right

  open CoarsePointwiseObservable public

  -- ACTUAL original two-link blocked holonomy respects every original
  -- fine bond; hence a coarse pointwise test is still a fine pointwise test.
  blockedPullbackPointwise :
    ∀ (observable : CoarseLinks → ℝ)
      (ext : CoarsePointwiseObservable observable) →
    GaugeHaar.PeriodicPointwiseObservable
      theory traceData exponential 3 betaFine
      oneLink bilateral (Codec.decodeOriginalBonds 4) divide
      (λ fine → observable (selectedBlock fine))
  blockedPullbackPointwise observable ext = record
    { GaugeHaar.PeriodicPointwiseObservable.congruentAt =
        λ left right same →
          sameAtAllBonds ext
            (selectedBlock left) (selectedBlock right)
            (Block.nativeBlockedPositiveLinksPointwise
              (Native.sunExactSignedLinkGroup theory)
              left right same)
    }

  -- The same ORIGINAL fine product-Haar Gibbs integration law is used.
  -- The coarse observable is a pullback, not a claimed coarse Wilson
  -- Gibbs distribution. This theorem has no field-function equality axiom.
  originalFineMeasureBlockedGaugeInvariant :
    ∀ (observable : CoarseLinks → ℝ)
      (ext : CoarsePointwiseObservable observable)
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        observable
          (selectedBlock
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine → observable (selectedBlock fine))
  originalFineMeasureBlockedGaugeInvariant observable ext gamma =
    Constructed.actualPeriodicGaugeNormalized
      theory traceData exponential 3 betaFine
      oneLink bilateral divide
      (λ fine → observable (selectedBlock fine))
      (blockedPullbackPointwise observable ext)
      gamma

  -- The ORIGINAL side-two Wilson action is a selected coarse observable;
  -- its pointwise congruence is already proved for every periodic n.
  blockedCoarseWilsonPointwise :
    (betaCoarse : ℝ) →
    CoarsePointwiseObservable
      (Variable.periodicSUNWilsonAction
        theory traceData 1 betaCoarse)
  blockedCoarseWilsonPointwise betaCoarse = record
    { sameAtAllBonds =
        Pointwise.variableWilsonActionPointwise
          theory traceData 1 betaCoarse
    }

  originalFineGibbsBlockedWilsonGaugeInvariant :
    ∀ betaCoarse
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNWilsonAction theory traceData 1 betaCoarse
          (selectedBlock
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNWilsonAction theory traceData 1 betaCoarse
          (selectedBlock fine))
  originalFineGibbsBlockedWilsonGaugeInvariant betaCoarse gamma =
    originalFineMeasureBlockedGaugeInvariant
      (Variable.periodicSUNWilsonAction
        theory traceData 1 betaCoarse)
      (blockedCoarseWilsonPointwise betaCoarse)
      gamma

  blockedCoarseGibbsPointwise :
    (betaCoarse : ℝ) →
    CoarsePointwiseObservable
      (Variable.periodicSUNGibbsDensity
        theory traceData exponential 1 betaCoarse)
  blockedCoarseGibbsPointwise betaCoarse = record
    { sameAtAllBonds =
        Pointwise.variableGibbsDensityPointwise
          theory traceData exponential 1 betaCoarse
    }

  originalFineGibbsBlockedGibbsGaugeInvariant :
    ∀ betaCoarse
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential 1 betaCoarse
          (selectedBlock
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡
    Physical.normalizedExpectation selectedFineMeasure
      (λ fine →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential 1 betaCoarse
          (selectedBlock fine))
  originalFineGibbsBlockedGibbsGaugeInvariant betaCoarse gamma =
    originalFineMeasureBlockedGaugeInvariant
      (Variable.periodicSUNGibbsDensity
        theory traceData exponential 1 betaCoarse)
      (blockedCoarseGibbsPointwise betaCoarse)
      gamma
