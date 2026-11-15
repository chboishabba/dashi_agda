module DASHI.Analysis.BishopOriginalEtaNativeFactorialExpSourceWeldExact where

------------------------------------------------------------------------
-- CROSS-PR ACTUAL SAME-TERM BRIDGE: BISHOP ETA (#1408) ↔ NATIVE EXP (#1478)
--
-- The original Round11 eta terms are *not* arbitrary chosen Cauchy
-- limits: they are the ACTUAL Bishop analytic complex exponential at
-- -s * canonicalNatLog(n+1). The #1478 theorem proves convergence of
-- the ORIGINAL factorial series on that very complex argument to
-- the SAME native bishopExp*cos/sin exponential.
--
-- The original Riemann carrier, the original setoid exponential
-- carrier and the original factorial-series carrier have different
-- constructors, but their re/im coordinates are definitionally
-- the same vendored Bishop reals. Prove exact component equality at
-- each source term, then obtain BOTH original factorial convergence
-- statements by transport of #1478, with no new analytic axiom.
--
-- This is a genuinely paid CROSS-SOURCE term identity. It is NOT
--   log(2n)=log(2)+log(n), exp(z+w)=exp(z)exp(w), or
--   dyadic a(2k+1)=2^(-s) a(k).
-- Hence it does NOT promote the original eta factor identity or
-- compact-uniform eta convergence. Golden Agda 2.9 acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; proj₁; proj₂)
import Real as R
import Sequence as Sequence

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as Analytic
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Series
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Analysis.BishopComplexExpFactEqualsNativeExpExact as ExpFact
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Factorial
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- The first concrete missing bridge: the original Riemann eta source
-- output is precisely the same native complex exponential as the
-- #1478 factorial limit, in BOTH coordinates. No approximation
-- or equality-reflection principle is invoked.
actualOriginalEtaExponentialRealIsNativeFactorialLimit :
  (T : Cartesian.BishopSetoidComplexTranscendentals)
  (logNat : Terms.NatLogCandidate)
  (s : Analytic.BishopComplex) (n : Nat) →
  Analytic.re (Terms.bishopDirichletExponentialTerm T logNat s n)
  ≡
  Series.re
    (Weld.originalBishopExpOnSeries T
      (Series.complex
        (Analytic.re (Terms.bishopNegativeSLn logNat s n))
        (Analytic.im (Terms.bishopNegativeSLn logNat s n))))
actualOriginalEtaExponentialRealIsNativeFactorialLimit T logNat s n = refl

actualOriginalEtaExponentialImagIsNativeFactorialLimit :
  (T : Cartesian.BishopSetoidComplexTranscendentals)
  (logNat : Terms.NatLogCandidate)
  (s : Analytic.BishopComplex) (n : Nat) →
  Analytic.im (Terms.bishopDirichletExponentialTerm T logNat s n)
  ≡
  Series.im
    (Weld.originalBishopExpOnSeries T
      (Series.complex
        (Analytic.re (Terms.bishopNegativeSLn logNat s n))
        (Analytic.im (Terms.bishopNegativeSLn logNat s n))))
actualOriginalEtaExponentialImagIsNativeFactorialLimit T logNat s n = refl

-- This is the stronger convergence consumer: factorial-series
-- convergence of the literal native eta term value, coordinate by
-- coordinate. The original term's actual canonical logarithm is
-- maintained, not substituted by an independently selected log.
actualOriginalEtaTermFactorialSeriesConverges :
  (T : Cartesian.BishopSetoidComplexTranscendentals)
  (logNat : Terms.NatLogCandidate)
  (s : Analytic.BishopComplex) (n : Nat) →
  Sequence._ConvergesTo_
    (Sequence.SeriesOf
      (Series.realTerms
        (Factorial.originalBishopFactorialComplexTerm
          (Series.complex
            (Analytic.re (Terms.bishopNegativeSLn logNat s n))
            (Analytic.im (Terms.bishopNegativeSLn logNat s n))))))
    (Analytic.re (Terms.bishopDirichletExponentialTerm T logNat s n))
  ×
  Sequence._ConvergesTo_
    (Sequence.SeriesOf
      (Series.imagTerms
        (Factorial.originalBishopFactorialComplexTerm
          (Series.complex
            (Analytic.re (Terms.bishopNegativeSLn logNat s n))
            (Analytic.im (Terms.bishopNegativeSLn logNat s n))))))
    (Analytic.im (Terms.bishopDirichletExponentialTerm T logNat s n))
actualOriginalEtaTermFactorialSeriesConverges T logNat s n =
  ExpFact.originalBishopExpFactEqualsNativeExp T
    (Analytic.re (Terms.bishopNegativeSLn logNat s n))
    (Analytic.im (Terms.bishopNegativeSLn logNat s n))

-- The EXACT selected original Round11 eta source, not a new term
-- family: consumes the real logarithm candidate actually constructed
-- by the negative-log source and the existing Round11 Machin choice.
module OriginalRound11
  (inputs : Round11.Round11BishopCutset)
  where

  module Selected = Eta.OriginalRound11DirichletEta inputs

  originalRound11EtaTermIsNativeExpReal :
    (s : Analytic.BishopComplex) (n : Nat) →
    Analytic.re (Selected.sourceTerms s n)
    ≡
    Series.re
      (Weld.originalBishopExpOnSeries
        (Route.round11MachinTranscendentals inputs)
        (Series.complex
          (Analytic.re (Terms.bishopNegativeSLn
            Terms.sourceCanonicalNatLogCandidate s n))
          (Analytic.im (Terms.bishopNegativeSLn
            Terms.sourceCanonicalNatLogCandidate s n))))
  originalRound11EtaTermIsNativeExpReal s n =
    actualOriginalEtaExponentialRealIsNativeFactorialLimit
      (Route.round11MachinTranscendentals inputs)
      Terms.sourceCanonicalNatLogCandidate s n

  -- Both genuine factorial-series component limits are now
  -- source-specific to the ORIGINAL eta term at each selected n.
  originalRound11EtaTermFactorialConvergence :
    (s : Analytic.BishopComplex) (n : Nat) →
    Sequence._ConvergesTo_
      (Sequence.SeriesOf
        (Series.realTerms
          (Factorial.originalBishopFactorialComplexTerm
            (Series.complex
              (Analytic.re (Terms.bishopNegativeSLn
                Terms.sourceCanonicalNatLogCandidate s n))
              (Analytic.im (Terms.bishopNegativeSLn
                Terms.sourceCanonicalNatLogCandidate s n))))))
      (Analytic.re (Selected.sourceTerms s n))
    ×
    Sequence._ConvergesTo_
      (Sequence.SeriesOf
        (Series.imagTerms
          (Factorial.originalBishopFactorialComplexTerm
            (Series.complex
              (Analytic.re (Terms.bishopNegativeSLn
                Terms.sourceCanonicalNatLogCandidate s n))
              (Analytic.im (Terms.bishopNegativeSLn
                Terms.sourceCanonicalNatLogCandidate s n))))))
      (Analytic.im (Selected.sourceTerms s n))
  originalRound11EtaTermFactorialConvergence s n =
    actualOriginalEtaTermFactorialSeriesConverges
      (Route.round11MachinTranscendentals inputs)
      Terms.sourceCanonicalNatLogCandidate s n
