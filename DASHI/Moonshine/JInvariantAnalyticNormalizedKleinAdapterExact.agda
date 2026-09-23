module DASHI.Moonshine.JInvariantAnalyticNormalizedKleinAdapterExact where

------------------------------------------------------------------------
-- STANDARD-j ANALYTIC KLEIN ADAPTER
--
-- Existing analytic owners distinguish two denominators:
--
--   D      = E4^3 - E6^2
--   Delta  = normalize(D), classically D / 1728.
--
-- JSameWeightQuotientInvariantExact.jRatio uses D directly.  The renderer and
-- the finite Eisenstein Klein owner use the standard modular-j normalization
--
--   j = E4^3 / Delta.
--
-- This module keeps that normalization distinction explicit and constructs a
-- KleinJAlgebra whose KleinJ is definitionally the normalized standard-j
-- quotient.  No identification with the Homann/Wolfram J=j/1728 convention is
-- made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as Normalized
import DASHI.Moonshine.JSameWeightQuotientInvariantExact as J
import DASHI.Moonshine.JSameWeightQuotientReflectionExact as JRef
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein

------------------------------------------------------------------------
-- 1. Standard normalized j.
------------------------------------------------------------------------

standardJ :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Normalized.WeightCompatibleNormalization M) →
  (Q : J.QuotientCancellationAlgebra M) →
  Eisenstein.Parameter M →
  Eisenstein.Scalar M
standardJ M A N Q tau =
  J._/ˢ_ Q
    (J.jNumerator M tau)
    (Normalized.normalizedDelta M A N tau)

------------------------------------------------------------------------
-- 2. Weight-zero modular invariance of the normalized quotient.
------------------------------------------------------------------------

standardJInvariant :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Normalized.WeightCompatibleNormalization M) →
  (Q : J.QuotientCancellationAlgebra M) →
  (g : Eisenstein.SL2Z) →
  (tau : Eisenstein.Parameter M) →
  J.ScalingSafe Q
    (Eisenstein.power M (Eisenstein.denominator M g tau) 12) →
  J.DenominatorSafe Q (Normalized.normalizedDelta M A N tau) →
  standardJ M A N Q (Eisenstein.actParameter M g tau)
  ≡
  standardJ M A N Q tau
standardJInvariant M A N Q g tau scaleSafe denominatorSafe =
  trans
    (cong₂ (J._/ˢ_ Q)
      (J.jNumeratorTransformation M A g tau)
      (Normalized.normalizedDeltaTransformsAtWeight12 M A N g tau))
    (J.cancelCommonScale Q
      (Eisenstein.power M (Eisenstein.denominator M g tau) 12)
      (J.jNumerator M tau)
      (Normalized.normalizedDelta M A N tau)
      scaleSafe
      denominatorSafe)

------------------------------------------------------------------------
-- 3. Reflection through a conjugation-compatible normalization.
------------------------------------------------------------------------

record NormalizedJReflectionAlgebra
    (M : Eisenstein.EisensteinAnalyticModel)
    (A : Disc.DiscriminantAlgebra M)
    (N : Normalized.WeightCompatibleNormalization M)
    (Q : J.QuotientCancellationAlgebra M) : Set₁ where
  field
    baseReflection :
      JRef.JReflectionAlgebra M A Q

    normalizeConjugate :
      (value : Eisenstein.Scalar M) →
      Normalized.normalize N
        (JRef.conjugate baseReflection value)
      ≡
      JRef.conjugate baseReflection
        (Normalized.normalize N value)

open NormalizedJReflectionAlgebra public

normalizedDeltaReflects :
  ∀ {M A N Q} →
  (R : NormalizedJReflectionAlgebra M A N Q) →
  (tau : Eisenstein.Parameter M) →
  Normalized.normalizedDelta M A N
    (JRef.reflectParameter (baseReflection R) tau)
  ≡
  JRef.conjugate (baseReflection R)
    (Normalized.normalizedDelta M A N tau)
normalizedDeltaReflects {M} {A} {N} R tau =
  trans
    (cong (Normalized.normalize N)
      (JRef.discriminantReflects (baseReflection R) tau))
    (normalizeConjugate R
      (Disc.unnormalisedDiscriminant M A tau))

standardJReflects :
  ∀ {M A N Q} →
  (R : NormalizedJReflectionAlgebra M A N Q) →
  (tau : Eisenstein.Parameter M) →
  standardJ M A N Q
    (JRef.reflectParameter (baseReflection R) tau)
  ≡
  JRef.conjugate (baseReflection R)
    (standardJ M A N Q tau)
standardJReflects {M} {A} {N} {Q} R tau =
  trans
    (cong₂ (J._/ˢ_ Q)
      (JRef.jNumeratorReflects (baseReflection R) tau)
      (normalizedDeltaReflects R tau))
    (JRef.conjugateQuotient
      (baseReflection R)
      (J.jNumerator M tau)
      (Normalized.normalizedDelta M A N tau))

------------------------------------------------------------------------
-- 4. Fixed-locus conjugation theorem.
------------------------------------------------------------------------

record StandardJReflectionFixedPoint
    {M : Eisenstein.EisensteinAnalyticModel}
    {A : Disc.DiscriminantAlgebra M}
    {N : Normalized.WeightCompatibleNormalization M}
    {Q : J.QuotientCancellationAlgebra M}
    (R : NormalizedJReflectionAlgebra M A N Q)
    (tau : Eisenstein.Parameter M) : Set where
  field
    fixed :
      JRef.reflectParameter (baseReflection R) tau ≡ tau

open StandardJReflectionFixedPoint public

standardJConjugationFixed :
  ∀ {M A N Q R tau} →
  StandardJReflectionFixedPoint {M} {A} {N} {Q} R tau →
  standardJ M A N Q tau
  ≡
  JRef.conjugate (baseReflection R)
    (standardJ M A N Q tau)
standardJConjugationFixed {M} {A} {N} {Q} {R} {tau} F =
  trans
    (cong (standardJ M A N Q)
      (Relation.Binary.PropositionalEquality.sym (fixed F)))
    (standardJReflects R tau)

------------------------------------------------------------------------
-- 5. Klein adapter.
--
-- The historical field name g2 is retained because that is the renderer's
-- source-facing Klein algebra slot.  Here it is explicitly instantiated with
-- normalized E4, matching the existing finite Eisenstein Klein owner.
------------------------------------------------------------------------

standardAnalyticKlein :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Normalized.WeightCompatibleNormalization M) →
  (Q : J.QuotientCancellationAlgebra M) →
  Klein.KleinJAlgebra
standardAnalyticKlein M A N Q =
  record
    { Klein.Point = Eisenstein.Parameter M
    ; Klein.Value = Eisenstein.Scalar M
    ; Klein.g2 = Disc.E4 M
    ; Klein.delta = Normalized.normalizedDelta M A N
    ; Klein.cube = Disc.cube M
    ; Klein.quotient = J._/ˢ_ Q
    }

standardAnalyticKleinJIsStandardJ :
  ∀ {M} →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Normalized.WeightCompatibleNormalization M) →
  (Q : J.QuotientCancellationAlgebra M) →
  (tau : Eisenstein.Parameter M) →
  Klein.KleinJ (standardAnalyticKlein M A N Q) tau
  ≡
  standardJ M A N Q tau
standardAnalyticKleinJIsStandardJ A N Q tau = refl

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

record AnalyticNormalizedKleinBoundary : Set where
  constructor analytic-normalized-klein-boundary
  field
    unnormalisedAndNormalisedJDistinguished : Bool
    standardJUsesNormalizedDelta : Bool
    standardJWeightZeroCompilerOwned : Bool
    normalizedDeltaReflectionCompilerOwned : Bool
    standardJReflectionCompilerOwned : Bool
    fixedLocusStandardJConjugationFixedOwned : Bool
    analyticKleinAdapterOwned : Bool
    analyticKleinJDefinitionallyStandardJ : Bool

    normalizationConjugationCompatibilityInhabitedHere : Bool
    rendererReadoutInstantiationOwnedHere : Bool
    wolframKleinJIdentifiedWithStandardJ : Bool

open AnalyticNormalizedKleinBoundary public

canonicalAnalyticNormalizedKleinBoundary :
  AnalyticNormalizedKleinBoundary
canonicalAnalyticNormalizedKleinBoundary =
  analytic-normalized-klein-boundary
    true true true true true true true true
    false false false
