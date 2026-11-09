module DASHI.Physics.YangMills.YMClayE1A3OriginalAllWordPathSupportExtensionalExact where

------------------------------------------------------------------------
-- E1/A3 genuine original Wilson ALL-WORD source support theorem.
--
-- Earlier source:
--   YMClayD1OriginalWilsonPathSupportExtensionalExact:
--      source-positive-bond locality for the ACTUAL signed Wilson loop.
--   YMClayE1D1OriginalVariablePlaquetteWordsExact:
--      arbitrary finite plaquette word on the SAME original Gibbs measure.
--
-- This module proves their missing all-word composition: if two ACTUAL
-- original changing-cutoff link fields agree on the finite union of
-- positively indexed bonds read by a selected plaquette word, that
-- original Wilson word has exactly the same REAL value on both fields.
--
-- Not assumed: free projective system, projective consistency, source
-- measure convergence, Wilson polymer decay, or OS mass gap.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayD1OriginalWilsonPathSupportExtensionalExact as Source
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words

appendSource : ∀ {A : Set} → List A → List A → List A
appendSource [] tail = tail
appendSource (x ∷ xs) tail = x ∷ appendSource xs tail

appendSourceLeft :
  ∀ {A : Set} {x : A} (left right : List A) →
  Torus._∈_ x left → Torus._∈_ x (appendSource left right)
appendSourceLeft [] right ()
appendSourceLeft (x ∷ xs) right Torus.here = Torus.here
appendSourceLeft (x ∷ xs) right (Torus.there member) =
  Torus.there (appendSourceLeft xs right member)

appendSourceRight :
  ∀ {A : Set} {x : A} (left right : List A) →
  Torus._∈_ x right → Torus._∈_ x (appendSource left right)
appendSourceRight [] right member = member
appendSourceRight (x ∷ xs) right member =
  Torus.there (appendSourceRight xs right member)

originalWordActualFlatPositiveBondSupport :
  ∀ {n} →
  List (Plaquette.PeriodicPlaquette n) →
  List (Torus.PositiveBond (suc n))
originalWordActualFlatPositiveBondSupport [] = []
originalWordActualFlatPositiveBondSupport (p ∷ ps) =
  appendSource (Source.sourcePlaquettePositiveBondSupport p)
    (originalWordActualFlatPositiveBondSupport ps)

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

  originalPlaquetteTraceSourceExtensional :
    (n : Nat) (p : Plaquette.PeriodicPlaquette n)
    (left right : Variable.SUNPeriodicLinks theory n) →
    (∀ bond →
      Torus._∈_ bond (Source.sourcePlaquettePositiveBondSupport p) →
      left bond ≡ right bond) →
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n (p ∷ []) left
    ≡
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n (p ∷ []) right
  originalPlaquetteTraceSourceExtensional n p left right same =
    cong₂ _*ℝ_
      (cong (Trace.matrixWilsonValue traceData)
        (Source.originalWilsonPlaquetteHolonomyExtensional
          (Variable.periodicSUNRealization theory n left
            (λ _ → SUN.sunIdentity theory))
          (Variable.periodicSUNRealization theory n right
            (λ _ → SUN.sunIdentity theory))
          p same))
      refl

  originalWordRealSourceExtensional :
    (n : Nat) (word : List (Plaquette.PeriodicPlaquette n))
    (left right : Variable.SUNPeriodicLinks theory n) →
    (∀ bond →
      Torus._∈_ bond (originalWordActualFlatPositiveBondSupport word) →
      left bond ≡ right bond) →
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n word left
    ≡
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n word right
  originalWordRealSourceExtensional n [] left right same = refl
  originalWordRealSourceExtensional n (p ∷ ps) left right same =
    cong₂ _*ℝ_
      (cong (Trace.matrixWilsonValue traceData)
        (Source.originalWilsonPlaquetteHolonomyExtensional
          (Variable.periodicSUNRealization theory n left
            (λ _ → SUN.sunIdentity theory))
          (Variable.periodicSUNRealization theory n right
            (λ _ → SUN.sunIdentity theory))
          p
          (λ bond inHead →
            same bond
              (appendSourceLeft
                (Source.sourcePlaquettePositiveBondSupport p)
                (originalWordActualFlatPositiveBondSupport ps)
                inHead))))
      (originalWordRealSourceExtensional n ps left right
        (λ bond inTail →
          same bond
            (appendSourceRight
              (Source.sourcePlaquettePositiveBondSupport p)
              (originalWordActualFlatPositiveBondSupport ps)
              inTail)))
