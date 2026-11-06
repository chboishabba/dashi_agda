module DASHI.Physics.YangMills.YMClayOriginalR445PublishedWilsonRPWordWeldExact where

------------------------------------------------------------------------
-- YM M.04 selected native R445 published Wilson RP compiler.
--
-- This is NOT an independently invented OS axiom. It uses the exact
-- published lattice Wilson RP authority already reified in
-- BalabanClayOSWilsonReflectionPositivityExact (Osterwalder--Seiler;
-- Menotti--Pelissetto), then maps the nonnegative result onto the
-- original 1024-bond Wilson-Gibbs reflected all-word Gram and its
-- EXACT native R445 pushforward.
--
-- Only one physical SAME-OBJECT boundary remains explicit:
-- the published Wilson action, time-reflection plane, admissible
-- gauge-invariant positive-time word, and original native Wilson
-- reflected expectation must be identified; no chosen equality
-- between arbitrary OS states is postulated.
--
-- This does not prove that identification, full positive-complex
-- GNS, physical continuum OS or continuum Yang-Mills OS Gram.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as Published
import DASHI.Physics.YangMills.YMClayOriginalR445ReflectedAllWordGramExact as Native

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  CoarseLinks : Set
  CoarseLinks =
    Native.CoarseLinks theory traceData exponential
      betaFine oneLink bilateral divide

  CoarseObservable : Set
  CoarseObservable = CoarseLinks → ℝ

  -- No fresh independent source word algebra: use the native
  -- reflected ALL-WORD structure from the actual Wilson source.
  originalReflectedWordGram :
    (CoarseObservable → CoarseObservable) →
    List CoarseObservable → List CoarseObservable → ℝ
  originalReflectedWordGram =
    Native.originalFineReflectedWordGram
      theory traceData exponential betaFine oneLink bilateral divide

  actualR445ReflectedWordGram :
    (CoarseObservable → CoarseObservable) →
    List CoarseObservable → List CoarseObservable → ℝ
  actualR445ReflectedWordGram =
    Native.nativeR445ReflectedWordGram
      theory traceData exponential betaFine oneLink bilateral divide

  originalPublishedWilsonRPYieldsNativePositiveWord :
    (published :
      Published.WilsonReflectionPositivityData CoarseObservable ℝ)
    (coarseReflect : CoarseObservable → CoarseObservable)
    (AdmissiblePositiveTimeWord : List CoarseObservable → Set)
    (wordGaugeInvariant :
      ∀ word →
      AdmissiblePositiveTimeWord word →
      Published.GaugeInvariant published
        (Native.coarseWord theory traceData exponential
          betaFine oneLink bilateral divide word))
    (wordPositiveTime :
      ∀ word →
      AdmissiblePositiveTimeWord word →
      Published.PositiveTimeObservable published
        (Native.coarseWord theory traceData exponential
          betaFine oneLink bilateral divide word))
    (publishedPositiveIsReal :
      ∀ value →
      Published.Nonnegative published value →
      0ℝ ≤ℝ value)
    (sourceIdentifiesActualWilsonReflection :
      ∀ word →
      AdmissiblePositiveTimeWord word →
      originalReflectedWordGram coarseReflect word word
      ≡ Published.reflectedProductExpectation published
          (Native.coarseWord theory traceData exponential
            betaFine oneLink bilateral divide word))
    (word : List CoarseObservable) →
    AdmissiblePositiveTimeWord word →
    0ℝ ≤ℝ actualR445ReflectedWordGram coarseReflect word word
  originalPublishedWilsonRPYieldsNativePositiveWord
      published coarseReflect AdmissiblePositiveTimeWord
      wordGaugeInvariant wordPositiveTime publishedPositiveIsReal
      sourceIdentifiesActualWilsonReflection word valid =
    Native.originalFineOSPositiveTransfersToNativeR445
      theory traceData exponential betaFine oneLink bilateral divide
      coarseReflect word
      (subst (λ value → 0ℝ ≤ℝ value)
        (sym (sourceIdentifiesActualWilsonReflection word valid))
        (publishedPositiveIsReal
          (Published.reflectedProductExpectation published
            (Native.coarseWord theory traceData exponential
              betaFine oneLink bilateral divide word))
          (Published.wilsonPositivityAtAnySeparationParity
            published Published.evenSitePlane
            (Native.coarseWord theory traceData exponential
              betaFine oneLink bilateral divide word)
            (wordGaugeInvariant word valid)
            (wordPositiveTime word valid))))

-- What must still be constructed on the literal physical source:
-- * exact published source action/normalization/positive-time plane
--   and gauge-invariant test dictionary (sourceIdentifies...);
-- * actual fine 1024-link physical reflection on the native
--   noncommutative blocked link map and its support;
-- * complex YM OS star/reflection and its positive-time algebra;
-- * complete nontrivial OS/GNS and physical continuum limits.
