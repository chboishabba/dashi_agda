module DASHI.Moonshine.JInvariant369JointJReflectionWeldExact where

------------------------------------------------------------------------
-- ANALYTIC SAME-WEIGHT j REFLECTION -> JOINT J/PHASE/LEVEL BUNDLE
--
-- The abstract analytic owner
--
--   JSameWeightQuotientReflectionExact
--
-- proves that the same-weight quotient
--
--   j = E4^3 / Delta
--
-- conjugates under a common E4/Delta reflection.  The joint 369 bundle has an
-- intentionally backend-agnostic exactJ field and a JointJConjugation socket.
--
-- This module is the missing typed weld between those two owners.
--
-- Nothing here identifies a renderer with the analytic model by resemblance.
-- A consumer must supply:
--
--   * a parameter map from renderer points to the analytic model;
--   * an embedding of analytic scalar j-values into renderer values;
--   * same-object equality of renderer j with the embedded analytic quotient;
--   * agreement of renderer reflection with analytic reflection;
--   * compatibility of the two conjugation operations.
--
-- From exactly those fields the joint j-conjugation theorem is compiled.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Delta
import DASHI.Moonshine.JSameWeightQuotientInvariantExact as J
import DASHI.Moonshine.JSameWeightQuotientReflectionExact as JRef

import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369ReflectionEquivarianceExact as Reflection
import DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact as Joint

------------------------------------------------------------------------
-- 1. Exact same-object weld.
------------------------------------------------------------------------

record JointJAnalyticReflectionWeld
    {R : Render.JPhaseRenderingAlgebra}
    {L : Tower.CanonicalLevel27Lift R}
    {W : Joint.JointReflectionAction R L}
    {M : Eisenstein.EisensteinAnalyticModel}
    {A : Delta.DiscriminantAlgebra M}
    {Q : J.QuotientCancellationAlgebra M}
    (AR : JRef.JReflectionAlgebra M A Q) : Set₁ where
  field
    parameterAt :
      Klein.Point (Render.klein R) →
      Eisenstein.Parameter M

    embedJ :
      Eisenstein.Scalar M →
      Klein.Value (Render.klein R)

    conjugateRenderer :
      Klein.Value (Render.klein R) →
      Klein.Value (Render.klein R)

    reflectedParameterAgrees :
      (z : Klein.Point (Render.klein R)) →
      parameterAt
        (Reflection.reflectPoint
          (Joint.phaseReflection W) z)
      ≡
      JRef.reflectParameter AR (parameterAt z)

    rendererJAgrees :
      (z : Klein.Point (Render.klein R)) →
      Render.jValue R z
      ≡
      embedJ
        (J.jRatio M A Q (parameterAt z))

    embedConjugateAgrees :
      (value : Eisenstein.Scalar M) →
      embedJ (JRef.conjugate AR value)
      ≡
      conjugateRenderer (embedJ value)

open JointJAnalyticReflectionWeld public

------------------------------------------------------------------------
-- 2. Compile the analytic quotient theorem into JointJConjugation.
------------------------------------------------------------------------

jointJConjugationFromAnalyticWeld :
  ∀ {R L W M A Q AR} →
  JointJAnalyticReflectionWeld
    {R = R} {L = L} {W = W}
    {M = M} {A = A} {Q = Q} AR →
  Joint.JointJConjugation W
jointJConjugationFromAnalyticWeld
    {R} {W = W} {M} {A} {Q} {AR} E =
  record
    { Joint.conjugateValue = conjugateRenderer E
    ; Joint.jConjugates = proof
    }
  where
  proof :
    (z : Klein.Point (Render.klein R)) →
    Render.jValue R
      (Reflection.reflectPoint
        (Joint.phaseReflection W) z)
    ≡
    conjugateRenderer E (Render.jValue R z)
  proof z =
    begin
      Render.jValue R
        (Reflection.reflectPoint
          (Joint.phaseReflection W) z)
        ≡⟨ rendererJAgrees E
              (Reflection.reflectPoint
                (Joint.phaseReflection W) z) ⟩
      embedJ E
        (J.jRatio M A Q
          (parameterAt E
            (Reflection.reflectPoint
              (Joint.phaseReflection W) z)))
        ≡⟨ cong
              (λ p → embedJ E (J.jRatio M A Q p))
              (reflectedParameterAgrees E z) ⟩
      embedJ E
        (J.jRatio M A Q
          (JRef.reflectParameter AR
            (parameterAt E z)))
        ≡⟨ cong (embedJ E)
              (JRef.jRatioReflects AR
                (parameterAt E z)) ⟩
      embedJ E
        (JRef.conjugate AR
          (J.jRatio M A Q (parameterAt E z)))
        ≡⟨ embedConjugateAgrees E
              (J.jRatio M A Q (parameterAt E z)) ⟩
      conjugateRenderer E
        (embedJ E
          (J.jRatio M A Q (parameterAt E z)))
        ≡⟨ cong (conjugateRenderer E)
              (sym (rendererJAgrees E z)) ⟩
      conjugateRenderer E (Render.jValue R z)
    ∎

------------------------------------------------------------------------
-- 3. Reflection fixed point -> joint exactJ is conjugation-fixed.
------------------------------------------------------------------------

jointJConjugationFixedAtRendererFixedPoint :
  ∀ {R L W M A Q AR} →
  (E :
    JointJAnalyticReflectionWeld
      {R = R} {L = L} {W = W}
      {M = M} {A = A} {Q = Q} AR) →
  (z : Klein.Point (Render.klein R)) →
  Reflection.reflectPoint (Joint.phaseReflection W) z ≡ z →
  Joint.exactJ (Joint.sampleAt L z)
  ≡
  conjugateRenderer E
    (Joint.exactJ (Joint.sampleAt L z))
jointJConjugationFixedAtRendererFixedPoint
    {L = L} {W = W} E z fixed =
  begin
    Joint.exactJ (Joint.sampleAt L z)
      ≡⟨ cong
            (λ point →
              Joint.exactJ (Joint.sampleAt L point))
            (sym fixed) ⟩
    Joint.exactJ
      (Joint.sampleAt L
        (Reflection.reflectPoint
          (Joint.phaseReflection W) z))
      ≡⟨ Joint.jointRJConjugates
            (jointJConjugationFromAnalyticWeld E) z ⟩
    conjugateRenderer E
      (Joint.exactJ (Joint.sampleAt L z))
  ∎

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

record JointJReflectionWeldBoundary : Set where
  constructor joint-j-reflection-weld-boundary
  field
    analyticSameWeightReflectionCompilerReused : Bool
    rendererAnalyticSameObjectWeldTyped : Bool
    analyticReflectionCompilesToJointJConjugation : Bool
    rendererFixedPointCompilesToJointJConjugationFixed : Bool

    concreteRendererAnalyticWeldInhabited : Bool
    unitCircleFixedPointIdentifiedOnRendererCarrier : Bool
    conjugationFixedInterpretedAsOrderedRealValueHere : Bool

open JointJReflectionWeldBoundary public

canonicalJointJReflectionWeldBoundary :
  JointJReflectionWeldBoundary
canonicalJointJReflectionWeldBoundary =
  joint-j-reflection-weld-boundary
    true true true true
    false false false
