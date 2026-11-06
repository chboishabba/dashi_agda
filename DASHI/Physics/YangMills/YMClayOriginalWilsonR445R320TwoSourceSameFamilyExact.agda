module DASHI.Physics.YangMills.YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact where

------------------------------------------------------------------------
-- Y.FIN.05 / R443 -> R445 -> R320 ORIGINAL-SOURCE TWO-MARKED WELD.
--
-- The n=3 member of the changing-cutoff original Wilson family is
-- definitionally the exact side-four 1024-positive-bond Gibbs measure
-- from the original native R445 blocking route.  The same original
-- non-Abelian ordered two-link block pulls both source marks back.
--
-- Therefore its actual finite FORMAL mixed-log jet is the original
-- blocked fine covariance, and (by the existing same-source R445/R320
-- theorem) the actual pushed coarse covariance.  No independent
-- coarse measure, alternative fine Wilson action, or J oracle.
--
-- The *analytic* differentiated CMP116 partition function, uniform
-- UV/IR limit, physical distance rate and OS gap remain separate.
-- RealAnalysisAxioms is a transitive physical scalar authority.
-- SOURCE-WRITTEN; Agda typechecking and transitive trust pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Wilson
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClaySUNR445BlockedPushforwardR320CovarianceExact as R320
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

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

  FineLinks : Set
  FineLinks = Wilson.SUNPeriodicLinks theory 3

  CoarseLinks : Set
  CoarseLinks = Wilson.SUNPeriodicLinks theory 1

  originalNativeBlock : FineLinks → CoarseLinks
  originalNativeBlock =
    R320.originalNativeBlock theory traceData exponential
      (beta 3) oneLink bilateral divide

  coarsePullback : (CoarseLinks → ℝ) → FineLinks → ℝ
  coarsePullback observable fine =
    observable (originalNativeBlock fine)

  -- This is a DEFINITIONAL SAME MEASURE equality, not just matching
  -- source types: both sides reduce to the same Constructed owner.
  originalVariableN3IsNativeR445FineMeasure :
    Original.originalWilsonMeasure
      theory traceData exponential beta oneLink bilateral divide 3
    ≡
    R320.originalFineGibbsMeasure
      theory traceData exponential (beta 3) oneLink bilateral divide
  originalVariableN3IsNativeR445FineMeasure = refl

  originalN3CumulantIsNativeBlockedFineCovariance :
    ∀ (left right : CoarseLinks → ℝ) →
    Cumulant.connectedCovariance
      (Original.originalWilsonMomentAlgebra
        theory traceData exponential beta oneLink bilateral divide 3)
      (coarsePullback left) (coarsePullback right)
    ≡
    R320.connectedCovarianceOfOriginalBlockedFine
      theory traceData exponential (beta 3)
      oneLink bilateral divide left right
  originalN3CumulantIsNativeBlockedFineCovariance left right = refl

  originalN3LiteralMixedLogJetIsNativeBlockedCovariance :
    ∀ (left right : CoarseLinks → ℝ) →
    let directions =
          Original.originalWilsonLiteralJetDirections
            theory traceData exponential beta oneLink bilateral divide 3
    in
    Cumulant.literalMixedSecondLogDerivative directions
      (Cumulant.sourceDirectionOf directions (coarsePullback left))
      (Cumulant.sourceDirectionOf directions (coarsePullback right))
    ≡
    R320.connectedCovarianceOfOriginalBlockedFine
      theory traceData exponential (beta 3)
      oneLink bilateral divide left right
  originalN3LiteralMixedLogJetIsNativeBlockedCovariance left right =
    trans
      (Original.originalWilsonMixedJetIsOriginalConnectedCumulant
        theory traceData exponential beta oneLink bilateral divide
        3 (coarsePullback left) (coarsePullback right))
      (originalN3CumulantIsNativeBlockedFineCovariance left right)

  -- R320's actual native R445 pushforward is used directly.  It is NOT
  -- replaced by an independently selected coarse Gibbs kernel.
  originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance :
    ∀ (left right : CoarseLinks → ℝ) →
    let directions =
          Original.originalWilsonLiteralJetDirections
            theory traceData exponential beta oneLink bilateral divide 3
    in
    Cumulant.literalMixedSecondLogDerivative directions
      (Cumulant.sourceDirectionOf directions (coarsePullback left))
      (Cumulant.sourceDirectionOf directions (coarsePullback right))
    ≡
    R320.connectedCovarianceOfActualPushforward
      theory traceData exponential (beta 3)
      oneLink bilateral divide left right
  originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance
    left right =
    trans
      (originalN3LiteralMixedLogJetIsNativeBlockedCovariance left right)
      (R320.actualR445BlockedCovarianceIsSameR320FiniteSource
        theory traceData exponential (beta 3)
        oneLink bilateral divide left right)
