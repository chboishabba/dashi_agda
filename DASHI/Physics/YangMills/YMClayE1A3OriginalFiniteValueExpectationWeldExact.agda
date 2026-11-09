module DASHI.Physics.YangMills.YMClayE1A3OriginalFiniteValueExpectationWeldExact where

------------------------------------------------------------------------
-- E1/A3: source-exact finite-value Wilson expectation weld.
--
-- Source objects (not independently selected probability laws):
--   * original n-dependent SU(N) Wilson Gibbs/Haar expectation;
--   * original signed-path positive-link finite value evaluator;
--   * same original n-dependent plaquette word and gauge action.
--
-- Source expectation extensionality is already proved from product
-- Haar integral congruence in YMClayOriginalVariableWilsonCovarianceSourceExact.
-- This composes that *actual* theorem with the all-word literal
-- finite-value evaluator. No arbitrary projective extension/limit.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as Wilson
import DASHI.Physics.YangMills.YMClayE1OriginalSUNDependentCylinderExact as E1
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words
import DASHI.Physics.YangMills.YMClayE1A3OriginalSignedPathValueEvaluatorExact as Evaluator
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
open import Relation.Binary.PropositionalEquality using (trans)

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

  directFiniteWilsonWord :
    (n : Nat) (word : List (Plaquette.PeriodicPlaquette n)) →
    Wilson.Test theory traceData exponential beta oneLink bilateral divide n
  directFiniteWilsonWord n word links =
    Evaluator.evaluateOriginalWilsonWord
      (Native.sunExactSignedLinkGroup theory)
      (Trace.matrixWilsonValue traceData)
      word
      (Evaluator.originalWilsonWordSampledValues
        theory traceData exponential beta oneLink bilateral divide
        n word links)

  -- Source exact: finite list-value evaluation cannot change the actual
  -- Wilson normalized expectation of an arbitrary plaquette word.
  originalDirectFiniteValueExpectationIsOriginalWilson :
    (n : Nat) (word : List (Plaquette.PeriodicPlaquette n)) →
    Wilson.expectation
      theory traceData exponential beta oneLink bilateral divide n
      (directFiniteWilsonWord n word)
    ≡
    Wilson.expectation
      theory traceData exponential beta oneLink bilateral divide n
      (Words.originalWordObservable
        theory traceData exponential beta oneLink bilateral divide
        n word)
  originalDirectFiniteValueExpectationIsOriginalWilson n word =
    Wilson.originalWilsonExpectationExtensional
      theory traceData exponential beta oneLink bilateral divide
      n
      (directFiniteWilsonWord n word)
      (Words.originalWordObservable
        theory traceData exponential beta oneLink bilateral divide
        n word)
      (Evaluator.originalWilsonWordDirectFiniteEvaluation
        theory traceData exponential beta oneLink bilateral divide
        n word)

  -- The same source expectation is also the actually selected E1
  -- dependent cylinder expectation at the original cutoff. There is
  -- no change of Gibbs measure, normalization or beta history.
  originalDirectFiniteValueExpectationIsOriginalE1Cylinder :
    (selected : Words.OriginalChangingWord
      theory traceData exponential beta oneLink bilateral divide)
    (n : Nat) →
    Wilson.expectation
      theory traceData exponential beta oneLink bilateral divide n
      (directFiniteWilsonWord n (selected n))
    ≡
    E1.actualOriginalWilsonCylinderExpectation
      theory traceData exponential beta oneLink bilateral divide
      n
      (Words.originalChangingWordSection
        theory traceData exponential beta oneLink bilateral divide
        selected)
  originalDirectFiniteValueExpectationIsOriginalE1Cylinder
      selected n =
    trans
      (originalDirectFiniteValueExpectationIsOriginalWilson
        n (selected n))
      refl
