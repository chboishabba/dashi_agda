module DASHI.Physics.YangMills.YMClayOriginalR445ReflectedWordCMP116BIDIExact where

------------------------------------------------------------------------
-- P0 STEELMAN BIDI: source-forward original Wilson mixed-J
--              == same-R445-measure reflected CENTERED OS form.
--
-- REVERSE TARGET: dense same-H OS autocorrelation bounds must refer to
-- the actual centered reflected cylinder state. At finite cutoff this
-- is a covariance, NOT an uncentered quadratic or a spectral gap.
--
-- FORWARD SOURCE: original changing-cutoff n=3 Wilson Gibbs and exact
-- n=3 R445 native block -> R320 pushforward two-J connected cumulant.
-- This builds no replacement Gibbs source, action, kernel or H.
--
-- Original producer identities are ALREADY in master:
--   YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact
--   YMClaySUNR445BlockedPushforwardR320CovarianceExact
--   YMClayE1D1OriginalVariablePlaquetteWordsExact
-- Selected reflection is the actual original SU(N) coarse bond-field
-- reflection from the new #1536 source module.
--
-- The equality is a finite definitional same-source join. It does NOT
-- construct published RP, a positive-time time-shift semigroup, a
-- CMP119 local analytic insertion dictionary, physical CMP116 decay,
-- the interacting continuum E1 limit, a dense OS sector or the gap.
-- This module is source-written, NOT Agda kernel accepted.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _-ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Wilson
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Jet
import DASHI.Physics.YangMills.YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact as Source
import DASHI.Physics.YangMills.YMClaySUNR445BlockedPushforwardR320CovarianceExact as R320
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.YMClayOriginalR445ReflectedPointwiseWordWeldExact as Reflect

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

  CoarseLinks : Set
  CoarseLinks = Wilson.SUNPeriodicLinks theory 1

  OriginalCoarsePlaquetteWord : Set
  OriginalCoarsePlaquetteWord =
    Words.PlaquetteWord
      theory traceData exponential beta oneLink bilateral divide 1

  -- Same original n=1 geometry observable, BUT the law used below
  -- is the R445 pushforward of the original n=3 Gibbs measure.
  -- NEVER replace the latter by the independent bare n=1 Gibbs law.
  originalWordValue :
    OriginalCoarsePlaquetteWord → CoarseLinks → ℝ
  originalWordValue word =
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide 1 word

  originalCoarseReflection : CoarseLinks → CoarseLinks
  originalCoarseReflection =
    Reflect.reflectOriginalCoarseLinks
      theory traceData exponential (beta 3) oneLink bilateral divide

  reflectedOriginalWord :
    OriginalCoarsePlaquetteWord → CoarseLinks → ℝ
  reflectedOriginalWord word coarse =
    originalWordValue word (originalCoarseReflection coarse)

  -- The correct CENTERED reflection form on the SAME pushforward.
  -- This is not a separate OS Hilbert inner product or a positivity
  -- claim: it is simply the actual original connected covariance.
  originalCenteredReflectedOSForm :
    OriginalCoarsePlaquetteWord → ℝ
  originalCenteredReflectedOSForm word =
    R320.actualPushedCoarseExpectation
      theory traceData exponential (beta 3)
      oneLink bilateral divide
      (λ coarse →
        reflectedOriginalWord word coarse *ℝ
        originalWordValue word coarse)
    -ℝ
    (R320.actualPushedCoarseExpectation
      theory traceData exponential (beta 3)
      oneLink bilateral divide (reflectedOriginalWord word)
     *ℝ
     R320.actualPushedCoarseExpectation
       theory traceData exponential (beta 3)
       oneLink bilateral divide (originalWordValue word))

  -- F0: reverse OS CENTERING == original SAME-SOURCE R320 covariance.
  originalCenteredReflectedOSIsOriginalR320 :
    ∀ word →
    originalCenteredReflectedOSForm word
    ≡
    R320.connectedCovarianceOfActualPushforward
      theory traceData exponential (beta 3)
      oneLink bilateral divide
      (reflectedOriginalWord word) (originalWordValue word)
  originalCenteredReflectedOSIsOriginalR320 word = refl

  -- F1: this is the exact ORIGINAL n=3 mixed-J physical-Wilson
  -- cumulant, not a rational toy or a second source. Reverse and
  -- forward now join at the same finite centered Wilson correlation.
  originalMixedJIsSameCenteredReflectedOS :
    ∀ word →
    let directions =
          Jet.originalWilsonLiteralJetDirections
            theory traceData exponential beta oneLink bilateral divide 3
        reflected = reflectedOriginalWord word
        unreflected = originalWordValue word
        lift = Source.coarsePullback
          theory traceData exponential beta oneLink bilateral divide
    in
    Cumulant.literalMixedSecondLogDerivative directions
      (Cumulant.sourceDirectionOf directions (lift reflected))
      (Cumulant.sourceDirectionOf directions (lift unreflected))
    ≡ originalCenteredReflectedOSForm word
  originalMixedJIsSameCenteredReflectedOS word =
    Source.originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance
      theory traceData exponential beta oneLink bilateral divide
      (reflectedOriginalWord word) (originalWordValue word)

  -- F2 obligations retained:
  -- (i) candidate site reflection = published fine Wilson RP plane;
  -- (ii) time translations and positive-time word grammar on this
  -- exact original source; (iii) actual CMP119 insertion dictionary
  -- and full small/large CMP116 common rate over ALL cutoffs;
  -- (iv) E1 source convergence / same-H D2 dense reconstruction.
