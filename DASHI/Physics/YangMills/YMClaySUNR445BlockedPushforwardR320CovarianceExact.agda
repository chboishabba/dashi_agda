module DASHI.Physics.YangMills.YMClaySUNR445BlockedPushforwardR320CovarianceExact where

------------------------------------------------------------------------
-- R445 -> R320: finite SAME ORIGINAL SU(N) BLOCKED CONNECTED COVARIANCE.
--
-- Instead of postulating a second coarse measure or a new covariance,
-- derive the exact duality directly from
-- YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact:
--
-- C_{B_* mu}(F,G)
--   = E_mu[(F o B)(G o B)] - E_mu[F o B] E_mu[G o B].
--
-- Here mu is the ACTUAL original native 1024-bond side-four Wilson-Gibbs
-- measure and B is the native non-Abelian side-four -> side-two SU(N)
-- ordered two-link block. No arbitrary coarse Wilson density is inserted.
-- The equality is definitional from the existing original pushforward.
--
-- The existing R278 connected-covariance convergence compiler applies
-- ONLY when a changing-cutoff family and bounded F,G,FG tests are
-- constructed on those SAME actual measures; fixed side-four lacks that.
-- In particular this finite identity does NOT infer mixed-J logZ
-- differentiation, CMP116 shell decay or R333/OS positive gap.
-- Source: Wilson; Bałaban; existing DASHI original R445 and R278.
-- SOURCE WRITTEN, no Agda kernel acceptance; transitive real axioms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _-ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
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
  FineLinks = Push.FineLinks
    theory traceData exponential betaFine oneLink bilateral divide

  CoarseLinks : Set
  CoarseLinks = Push.CoarseLinks
    theory traceData exponential betaFine oneLink bilateral divide

  originalFineGibbsMeasure : Physical.PhysicalFiniteYMMeasure FineLinks ℝ
  originalFineGibbsMeasure =
    Push.originalFineGibbsMeasure
      theory traceData exponential betaFine oneLink bilateral divide

  originalNativeBlock : FineLinks → CoarseLinks
  originalNativeBlock =
    Push.actualBlockedLinkMap
      theory traceData exponential betaFine oneLink bilateral divide

  originalBlockedFineExpectation :
    (CoarseLinks → ℝ) → ℝ
  originalBlockedFineExpectation observable =
    Physical.normalizedExpectation originalFineGibbsMeasure
      (λ fine → observable (originalNativeBlock fine))

  actualPushedCoarseExpectation :
    (CoarseLinks → ℝ) → ℝ
  actualPushedCoarseExpectation =
    Push.actualPushforwardNormalized
      theory traceData exponential betaFine oneLink bilateral divide

  -- This is a SAME-OBJECT equality, not an assumed transfer theorem.
  originalBlockedFineExpectationIsPushforward :
    ∀ observable →
    originalBlockedFineExpectation observable
    ≡ actualPushedCoarseExpectation observable
  originalBlockedFineExpectationIsPushforward observable = refl

  connectedCovarianceOfOriginalBlockedFine :
    (CoarseLinks → ℝ) → (CoarseLinks → ℝ) → ℝ
  connectedCovarianceOfOriginalBlockedFine left right =
    originalBlockedFineExpectation
      (λ coarse → left coarse *ℝ right coarse)
      -ℝ
      (originalBlockedFineExpectation left
        *ℝ originalBlockedFineExpectation right)

  connectedCovarianceOfActualPushforward :
    (CoarseLinks → ℝ) → (CoarseLinks → ℝ) → ℝ
  connectedCovarianceOfActualPushforward left right =
    actualPushedCoarseExpectation
      (λ coarse → left coarse *ℝ right coarse)
      -ℝ
      (actualPushedCoarseExpectation left
        *ℝ actualPushedCoarseExpectation right)

  actualR445BlockedCovarianceIsSameR320FiniteSource :
    ∀ left right →
    connectedCovarianceOfOriginalBlockedFine left right
    ≡ connectedCovarianceOfActualPushforward left right
  actualR445BlockedCovarianceIsSameR320FiniteSource left right = refl

-- Physical changing-cutoff continuum and differentiated mixed-J
-- CMP116 estimates are STILL OPEN and cannot be obtained via this refl.
