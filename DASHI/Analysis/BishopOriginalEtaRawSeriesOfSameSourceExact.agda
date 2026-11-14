module DASHI.Analysis.BishopOriginalEtaRawSeriesOfSameSourceExact where

------------------------------------------------------------------------
-- ACTUAL ROUND11 RAW ETA PREFIX = MURRAY Sequence.SeriesOf.
--
-- The previous original source lemmas own all finite odd/even
-- prefix algebra, but their output is a BishopComplex cumulative
-- sum. This source shows its real and imaginary components are the
-- LITERAL pinned Bishop Sequence.SeriesOf cutoffs for the same terms.
--
-- No abstract convergence, order, norm, exponent, alternate log or
-- synthetic complex quotient is invoked. The eventual compact
-- uniform eta limit still requires a real analytic modulus and
-- Murray/Bishop completion/continuity proof.
-- SOURCE-WRITTEN, pinned Agda 2.9 kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Sequence as Seq
import Real as Real

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopOriginalEtaRawAllCutoffPrefixExact as Raw
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

originalRawRealTerm :
  (Nat → BC.BishopComplex) → Nat → Real.ℝ
originalRawRealTerm term n =
  BC.re (Raw.originalAlternatingRawTerm term n)

originalRawImagTerm :
  (Nat → BC.BishopComplex) → Nat → Real.ℝ
originalRawImagTerm term n =
  BC.im (Raw.originalAlternatingRawTerm term n)

-- Both equalities are INTENSIONAL, since the actual Cartesian
-- pair addition is defined coordinatewise by the SAME Bishop sum
-- used in Sequence.SeriesOf. This is not an analytic equality.
originalRawPrefixEqualsNativeSeriesOf :
  (term : Nat → BC.BishopComplex) (n : Nat) →
  (BC.re (Raw.originalRawEtaPrefix term n)
    ≡ Seq.SeriesOf (originalRawRealTerm term) n)
  ×
  (BC.im (Raw.originalRawEtaPrefix term n)
    ≡ Seq.SeriesOf (originalRawImagTerm term) n)
originalRawPrefixEqualsNativeSeriesOf term zero =
  refl , refl
originalRawPrefixEqualsNativeSeriesOf term (suc n)
  rewrite proj₁ (originalRawPrefixEqualsNativeSeriesOf term n)
        | proj₂ (originalRawPrefixEqualsNativeSeriesOf term n) =
  refl , refl

module OriginalRound11 (inputs : Round11.Round11BishopCutset) where
  module Selected = Eta.OriginalRound11DirichletEta inputs

  originalRound11EtaRawPrefixSameNativeSeries :
    (s : BC.BishopComplex) (n : Nat) →
    (BC.re
       (Raw.originalRawEtaPrefix (Selected.sourceTerms s) n)
       ≡ Seq.SeriesOf
         (originalRawRealTerm (Selected.sourceTerms s)) n)
    ×
    (BC.im
       (Raw.originalRawEtaPrefix (Selected.sourceTerms s) n)
       ≡ Seq.SeriesOf
         (originalRawImagTerm (Selected.sourceTerms s)) n)
  originalRound11EtaRawPrefixSameNativeSeries s n =
    originalRawPrefixEqualsNativeSeriesOf (Selected.sourceTerms s) n

-- Use together with Raw.actualOriginalRound11RawEvenPrefix and
-- Raw.actualOriginalRound11RawOddPrefix. These provide, on exactly
-- the source canonicalNatLogCandidate/expC,
--   NativeSeriesOf(2n) ~= etaPairs(n)
--   NativeSeriesOf(2n+1) ~= etaPairs(n) + term(2n),
-- coordinatewise. Convergence and holomorphy are NOT shown here.
