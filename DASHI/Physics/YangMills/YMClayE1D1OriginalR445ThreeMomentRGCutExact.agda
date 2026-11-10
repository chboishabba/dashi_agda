module DASHI.Physics.YangMills.YMClayE1D1OriginalR445ThreeMomentRGCutExact where

------------------------------------------------------------------------
-- E1 / D1 ORIGINAL R445 TWO-SOURCE RG MAXIMUM CUT.
--
-- The original source-first mixed-log J11 germ at Wilson side-four
-- is ALREADY proved equal to the actual R445 effective pushed-forward
-- covariance in YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact.
-- This module does NOT duplicate that proof, or assume a new measure.
--
-- It proves an exact, same-original-source 3-moment RG reduction:
--
--   if the original side-four Wilson effective coarse functional and
--   the original bare side-two Wilson functional agree on F,G,F*G,
--   then their connected covariance agrees, hence so does the original
--   source-first fine two-J mixed-log germ.
--
-- This does NOT assert those three physical RG equalities are true.
-- In general interacting block-RG generates extra action operators.
-- They are the new explicit unpaid quantitative leaves (eventually
-- controlled errors rather than exact equalities) on the actual
-- original Wilson path.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans; sym)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; _*ℝ_; _-ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayE1A3OriginalR445CrossCutoffSourceExact as Cross
import DASHI.Physics.YangMills.YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact as Same
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as Bare
import DASHI.Physics.YangMills.YMClaySUNR445BlockedPushforwardR320CovarianceExact as R320
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words
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

  CoarseTest : Set
  CoarseTest = Cross.CoarseTest
    theory traceData exponential beta oneLink bilateral divide

  sourceEffectiveExpectation : CoarseTest → ℝ
  sourceEffectiveExpectation =
    Cross.originalR445EffectiveCoarseExpectation
      theory traceData exponential beta oneLink bilateral divide

  sourceBareExpectation : CoarseTest → ℝ
  sourceBareExpectation =
    Cross.originalE1BareCoarseExpectation
      theory traceData exponential beta oneLink bilateral divide

  sourceCoarseProduct : CoarseTest → CoarseTest → CoarseTest
  sourceCoarseProduct left right coarse =
    left coarse *ℝ right coarse

  sourceEffectiveCovariance : CoarseTest → CoarseTest → ℝ
  sourceEffectiveCovariance left right =
    sourceEffectiveExpectation (sourceCoarseProduct left right)
    -ℝ
    (sourceEffectiveExpectation left *ℝ sourceEffectiveExpectation right)

  sourceBareCovariance : CoarseTest → CoarseTest → ℝ
  sourceBareCovariance left right =
    sourceBareExpectation (sourceCoarseProduct left right)
    -ℝ
    (sourceBareExpectation left *ℝ sourceBareExpectation right)

  -- Both covariance definitions are on the original selected sources.
  -- The effective side is the genuine R445 pushforward, while the
  -- bare side is the genuinely different original beta(1) Gibbs law.
  sourceEffectiveCovarianceIsActualR445 :
    (left right : CoarseTest) →
    sourceEffectiveCovariance left right
    ≡
    R320.connectedCovarianceOfActualPushforward
      theory traceData exponential (beta 3)
      oneLink bilateral divide left right
  sourceEffectiveCovarianceIsActualR445 left right =
    refl

  sourceBareCovarianceIsOriginalWilson :
    (left right : CoarseTest) →
    sourceBareCovariance left right
    ≡
    Bare.originalWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide
      1 left right
  sourceBareCovarianceIsOriginalWilson left right =
    refl

  -- One nonempty, SAME-SOURCE set of analytic RG hypotheses suffices
  -- for the connected two-source comparison. The proof does not
  -- add an independent covariance correspondence as an assumption.
  originalThreeRGEqualMomentsImplyCovariance :
    (left right : CoarseTest) →
    sourceEffectiveExpectation left ≡ sourceBareExpectation left →
    sourceEffectiveExpectation right ≡ sourceBareExpectation right →
    sourceEffectiveExpectation (sourceCoarseProduct left right)
      ≡ sourceBareExpectation (sourceCoarseProduct left right) →
    sourceEffectiveCovariance left right
      ≡ sourceBareCovariance left right
  originalThreeRGEqualMomentsImplyCovariance
    left right leftMoment rightMoment productMoment =
    cong₂ _-ℝ_
      productMoment
      (cong₂ _*ℝ_ leftMoment rightMoment)

  -- The SAME physical SU(N) fine Wilson mixed-log formal source J11
  -- (not an invented second J, coarse Hamiltonian or rational kernel)
  -- is now reduced to the three original coarse moment comparisons.
  originalThreeRGEqualMomentsWeldFineJetToBareCoarseCovariance :
    (left right : CoarseTest) →
    sourceEffectiveExpectation left ≡ sourceBareExpectation left →
    sourceEffectiveExpectation right ≡ sourceBareExpectation right →
    sourceEffectiveExpectation (sourceCoarseProduct left right)
      ≡ sourceBareExpectation (sourceCoarseProduct left right) →
    let directions =
          Original.originalWilsonLiteralJetDirections
            theory traceData exponential beta oneLink bilateral divide 3
    in
    Cumulant.literalMixedSecondLogDerivative directions
      (Cumulant.sourceDirectionOf directions
        (Same.coarsePullback
          theory traceData exponential beta oneLink bilateral divide
          left))
      (Cumulant.sourceDirectionOf directions
        (Same.coarsePullback
          theory traceData exponential beta oneLink bilateral divide
          right))
    ≡
    Bare.originalWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide
      1 left right
  originalThreeRGEqualMomentsWeldFineJetToBareCoarseCovariance
    left right leftMoment rightMoment productMoment =
    trans
      (Same.originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance
        theory traceData exponential beta oneLink bilateral divide
        left right)
      (trans
        (sym
          (sourceEffectiveCovarianceIsActualR445 left right))
        (trans
          (originalThreeRGEqualMomentsImplyCovariance
            left right leftMoment rightMoment productMoment)
          (sourceBareCovarianceIsOriginalWilson left right)))

  -- Concrete native source-Wilson word family on the actual side-two
  -- periodic 4-torus. This is the P0 original Wilson local test class,
  -- not arbitrary independent coarse sources.
  coarseOriginalWordTest :
    Words.PlaquetteWord
      theory traceData exponential beta oneLink bilateral divide 1 →
    CoarseTest
  coarseOriginalWordTest word =
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide 1 word

  originalThreeRGWordMomentMatchesWeldFineJet :
    (leftWord rightWord :
      Words.PlaquetteWord
        theory traceData exponential beta oneLink bilateral divide 1) →
    let left = coarseOriginalWordTest leftWord
        right = coarseOriginalWordTest rightWord
    in
    sourceEffectiveExpectation left ≡ sourceBareExpectation left →
    sourceEffectiveExpectation right ≡ sourceBareExpectation right →
    sourceEffectiveExpectation (sourceCoarseProduct left right)
      ≡ sourceBareExpectation (sourceCoarseProduct left right) →
    let directions =
          Original.originalWilsonLiteralJetDirections
            theory traceData exponential beta oneLink bilateral divide 3
        left = coarseOriginalWordTest leftWord
        right = coarseOriginalWordTest rightWord
    in
    Cumulant.literalMixedSecondLogDerivative directions
      (Cumulant.sourceDirectionOf directions
        (Same.coarsePullback
          theory traceData exponential beta oneLink bilateral divide
          left))
      (Cumulant.sourceDirectionOf directions
        (Same.coarsePullback
          theory traceData exponential beta oneLink bilateral divide
          right))
    ≡
    Bare.originalWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide
      1 left right
  originalThreeRGWordMomentMatchesWeldFineJet
    leftWord rightWord matchLeft matchRight matchProduct =
    originalThreeRGEqualMomentsWeldFineJetToBareCoarseCovariance
      (coarseOriginalWordTest leftWord)
      (coarseOriginalWordTest rightWord)
      matchLeft matchRight matchProduct
