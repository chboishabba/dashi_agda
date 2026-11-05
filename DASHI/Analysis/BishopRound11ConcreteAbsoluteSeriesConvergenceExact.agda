{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopRound11ConcreteAbsoluteSeriesConvergenceExact where

------------------------------------------------------------------------
-- K05: ACTUAL ROUND11 ABSOLUTE SINE/COSINE CONVERGENCE.
--
-- The original Round11 cutset already owns proof-bearing global
-- absolute convergence for its elementary sine/cosine terms, and
-- exact pointwise identification of those terms with the concrete
-- alternating signed factorial-power terms.
--
-- Transport the existing convergence along native setoid equality.
-- Do not replace the series with another complex or rational object.
--
-- Attribution: Bishop and Bridges, Murray (2022), Csimma pinned
-- Bishop backend, and the original DASHI Round11 term authors.
-- Source-written; exact-head Agda kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as T
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

concreteCosineAbsoluteTerms :
  R.ℝ → Nat → R.ℝ
concreteCosineAbsoluteTerms x n =
  R.∣ T.cosineSignedTerm x n ∣

concreteSineAbsoluteTerms :
  R.ℝ → Nat → R.ℝ
concreteSineAbsoluteTerms x n =
  R.∣ T.sineSignedTerm x n ∣

originalCosineAbsoluteTermEquivalent :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  (n : Nat) →
  R._≃_
    (R.∣ E.cosineTerm (Round11.elementarySeries inputs) x n ∣)
    (concreteCosineAbsoluteTerms x n)
originalCosineAbsoluteTermEquivalent inputs x n =
  RP.∣-∣-cong
    (T.cosineTermIsConcrete
      (Round11.round11ConcreteTermIdentification inputs)
      x n)

originalSineAbsoluteTermEquivalent :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  (n : Nat) →
  R._≃_
    (R.∣ E.sineTerm (Round11.elementarySeries inputs) x n ∣)
    (concreteSineAbsoluteTerms x n)
originalSineAbsoluteTermEquivalent inputs x n =
  RP.∣-∣-cong
    (T.sineTermIsConcrete
      (Round11.round11ConcreteTermIdentification inputs)
      x n)

concreteCosineAbsolutePartialEquivalent :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  (count : Nat) →
  R._≃_
    (Seq.SeriesOf
      (λ n →
        R.∣ E.cosineTerm (Round11.elementarySeries inputs) x n ∣)
      count)
    (Seq.SeriesOf (concreteCosineAbsoluteTerms x) count)
concreteCosineAbsolutePartialEquivalent inputs x =
  Ext.seriesPartialSumsCongruent
    (originalCosineAbsoluteTermEquivalent inputs x)

concreteSineAbsolutePartialEquivalent :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  (count : Nat) →
  R._≃_
    (Seq.SeriesOf
      (λ n →
        R.∣ E.sineTerm (Round11.elementarySeries inputs) x n ∣)
      count)
    (Seq.SeriesOf (concreteSineAbsoluteTerms x) count)
concreteSineAbsolutePartialEquivalent inputs x =
  Ext.seriesPartialSumsCongruent
    (originalSineAbsoluteTermEquivalent inputs x)

-- The selected Round11 absolute-convergence fields reduce to the
-- actual pinned Sequence convergence of the absolute term partials.
-- The two target witnesses use the original source limit.
round11ConcreteCosineAbsoluteConvergent :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  Seq._isConvergent (Seq.SeriesOf (concreteCosineAbsoluteTerms x))
round11ConcreteCosineAbsoluteConvergent inputs x =
  let
    original =
      E.cosineAbsoluteConvergence (Round11.elementarySeries inputs) x
  in
  proj₁ original ,
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) →
      concreteCosineAbsolutePartialEquivalent inputs x (suc n)})
    original

round11ConcreteSineAbsoluteConvergent :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  Seq._isConvergent (Seq.SeriesOf (concreteSineAbsoluteTerms x))
round11ConcreteSineAbsoluteConvergent inputs x =
  let
    original =
      E.sineAbsoluteConvergence (Round11.elementarySeries inputs) x
  in
  proj₁ original ,
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) →
      concreteSineAbsolutePartialEquivalent inputs x (suc n)})
    original
