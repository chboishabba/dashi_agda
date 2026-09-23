module DASHI.Moonshine.JInvariant369NormalizedAnalyticRendererExact where

------------------------------------------------------------------------
-- NORMALIZED STANDARD-j RENDERER ADAPTER
--
-- JInvariantAnalyticNormalizedKleinAdapterExact constructs the analytic
-- Klein algebra whose KleinJ is literally
--
--   standardJ = E4^3 / normalizedDelta.
--
-- This module lifts that algebra into the generic 369 renderer.  The readout
-- package supplies only representation/colour/finite-observer choices; it does
-- not own j itself.
--
-- As a result:
--
--   Render.jValue (standardRenderer ...) tau
--
-- reduces to the normalized analytic standardJ by construction.
--
-- This is intentionally separate from the older unnormalized jRatio weld and
-- from the Homann/Wolfram J = standard-j / 1728 calibration.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym)

import Base369 as Base
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as Normalized
import DASHI.Moonshine.JSameWeightQuotientInvariantExact as J
import DASHI.Moonshine.JSameWeightQuotientReflectionExact as JRef
import DASHI.Moonshine.JInvariantAnalyticNormalizedKleinAdapterExact as Standard

import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369ReflectionEquivarianceExact as Reflection
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact as Joint

------------------------------------------------------------------------
-- 1. Renderer readout only: j semantics are not supplied here.
------------------------------------------------------------------------

record StandardJRendererReadout
    (M : Eisenstein.EisensteinAnalyticModel) : Set₁ where
  field
    Scalar : Set
    Phase : Set
    Tone : Set
    Colour : Set

    realPart : Eisenstein.Scalar M → Scalar
    imagPart : Eisenstein.Scalar M → Scalar
    atan2 : Scalar → Scalar → Phase
    toneOfValue : Eisenstein.Scalar M → Tone

    phaseColour : Phase → Colour
    composeTone : Tone → Colour → Colour

    phase3 : Phase → Triadic.KernelTrit
    phase6 : Phase → Base.HexTruth
    phase9 : Phase → Triadic.NineSheet
    phase27 : Phase → Fabric.Ternary27Point

open StandardJRendererReadout public

standardRenderer :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (A : Disc.DiscriminantAlgebra M) →
  (N : Normalized.WeightCompatibleNormalization M) →
  (Q : J.QuotientCancellationAlgebra M) →
  StandardJRendererReadout M →
  Render.JPhaseRenderingAlgebra
standardRenderer M A N Q O =
  record
    { Render.klein =
        Standard.standardAnalyticKlein M A N Q

    ; Render.Scalar = Scalar O
    ; Render.Phase = Phase O
    ; Render.Tone = Tone O
    ; Render.Colour = Colour O

    ; Render.realPart = realPart O
    ; Render.imagPart = imagPart O
    ; Render.atan2 = atan2 O
    ; Render.toneOfValue = toneOfValue O

    ; Render.phaseColour = phaseColour O
    ; Render.composeTone = composeTone O

    ; Render.phase3 = phase3 O
    ; Render.phase6 = phase6 O
    ; Render.phase9 = phase9 O
    ; Render.phase27 = phase27 O
    }

standardRendererPointIsAnalyticParameter :
  ∀ {M A N Q O} →
  Klein.Point
    (Render.klein (standardRenderer M A N Q O))
  ≡
  Eisenstein.Parameter M
standardRendererPointIsAnalyticParameter = refl

standardRendererValueIsAnalyticScalar :
  ∀ {M A N Q O} →
  Klein.Value
    (Render.klein (standardRenderer M A N Q O))
  ≡
  Eisenstein.Scalar M
standardRendererValueIsAnalyticScalar = refl

standardRendererJValueIsStandardJ :
  ∀ {M}
    (A : Disc.DiscriminantAlgebra M)
    (N : Normalized.WeightCompatibleNormalization M)
    (Q : J.QuotientCancellationAlgebra M)
    (O : StandardJRendererReadout M)
    (tau : Eisenstein.Parameter M) →
  Render.jValue
    (standardRenderer M A N Q O)
    tau
  ≡
  Standard.standardJ M A N Q tau
standardRendererJValueIsStandardJ A N Q O tau = refl

------------------------------------------------------------------------
-- 2. Reflection alignment is now the ONLY j same-object input.
--
-- The renderer and analytic point/value carriers are definitionally the same.
-- A joint reflection action must merely use the same point involution as the
-- normalized analytic reflection algebra.
------------------------------------------------------------------------

record NormalizedRendererReflectionAlignment
    {M : Eisenstein.EisensteinAnalyticModel}
    {A : Disc.DiscriminantAlgebra M}
    {N : Normalized.WeightCompatibleNormalization M}
    {Q : J.QuotientCancellationAlgebra M}
    (O : StandardJRendererReadout M)
    (AR : Standard.NormalizedJReflectionAlgebra M A N Q)
    {L : Tower.CanonicalLevel27Lift
      (standardRenderer M A N Q O)}
    (W : Joint.JointReflectionAction
      (standardRenderer M A N Q O) L) : Set₁ where
  field
    reflectionPointAgrees :
      (tau : Eisenstein.Parameter M) →
      Reflection.reflectPoint
        (Joint.phaseReflection W) tau
      ≡
      JRef.reflectParameter
        (Standard.baseReflection AR) tau

open NormalizedRendererReflectionAlignment public

------------------------------------------------------------------------
-- 3. Standard-j reflection compiles directly into the joint bundle.
------------------------------------------------------------------------

jointJConjugationFromNormalizedRenderer :
  ∀ {M A N Q O AR L W} →
  (E :
    NormalizedRendererReflectionAlignment
      {M = M} {A = A} {N = N} {Q = Q}
      O AR {L = L} W) →
  Joint.JointJConjugation W
jointJConjugationFromNormalizedRenderer
    {M} {A} {N} {Q} {O} {AR} {W = W} E =
  record
    { Joint.conjugateValue =
        JRef.conjugate (Standard.baseReflection AR)
    ; Joint.jConjugates = proof
    }
  where
  R = standardRenderer M A N Q O

  proof :
    (tau : Eisenstein.Parameter M) →
    Render.jValue R
      (Reflection.reflectPoint
        (Joint.phaseReflection W) tau)
    ≡
    JRef.conjugate (Standard.baseReflection AR)
      (Render.jValue R tau)
  proof tau =
    begin
      Render.jValue R
        (Reflection.reflectPoint
          (Joint.phaseReflection W) tau)
        ≡⟨ standardRendererJValueIsStandardJ
              A N Q O
              (Reflection.reflectPoint
                (Joint.phaseReflection W) tau) ⟩
      Standard.standardJ M A N Q
        (Reflection.reflectPoint
          (Joint.phaseReflection W) tau)
        ≡⟨ cong (Standard.standardJ M A N Q)
              (reflectionPointAgrees E tau) ⟩
      Standard.standardJ M A N Q
        (JRef.reflectParameter
          (Standard.baseReflection AR) tau)
        ≡⟨ Standard.standardJReflects AR tau ⟩
      JRef.conjugate (Standard.baseReflection AR)
        (Standard.standardJ M A N Q tau)
        ≡⟨ cong
              (JRef.conjugate
                (Standard.baseReflection AR))
              (sym
                (standardRendererJValueIsStandardJ
                  A N Q O tau)) ⟩
      JRef.conjugate (Standard.baseReflection AR)
        (Render.jValue R tau)
    ∎

------------------------------------------------------------------------
-- 4. Fixed renderer reflection point -> standard j is conjugation-fixed.
------------------------------------------------------------------------

standardRendererJConjugationFixed :
  ∀ {M A N Q O AR L W} →
  (E :
    NormalizedRendererReflectionAlignment
      {M = M} {A = A} {N = N} {Q = Q}
      O AR {L = L} W) →
  (tau : Eisenstein.Parameter M) →
  Reflection.reflectPoint (Joint.phaseReflection W) tau ≡ tau →
  Joint.exactJ (Joint.sampleAt L tau)
  ≡
  JRef.conjugate (Standard.baseReflection AR)
    (Joint.exactJ (Joint.sampleAt L tau))
standardRendererJConjugationFixed
    {AR = AR} {L = L} {W = W} E tau fixed =
  begin
    Joint.exactJ (Joint.sampleAt L tau)
      ≡⟨ cong
            (λ point →
              Joint.exactJ (Joint.sampleAt L point))
            (sym fixed) ⟩
    Joint.exactJ
      (Joint.sampleAt L
        (Reflection.reflectPoint
          (Joint.phaseReflection W) tau))
      ≡⟨ Joint.jointRJConjugates
            (jointJConjugationFromNormalizedRenderer E)
            tau ⟩
    JRef.conjugate (Standard.baseReflection AR)
      (Joint.exactJ (Joint.sampleAt L tau))
  ∎

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record NormalizedAnalyticRendererBoundary : Set where
  constructor normalized-analytic-renderer-boundary
  field
    standardJRendererConstructorOwned : Bool
    rendererPointIsAnalyticParameterDefinitionally : Bool
    rendererValueIsAnalyticScalarDefinitionally : Bool
    rendererJValueIsStandardJDefinitionally : Bool
    jointJReflectionNeedsOnlyPointAlignment : Bool
    jointJConjugationCompilerOwned : Bool
    fixedPointConjugationCompilerOwned : Bool

    concreteReadoutInhabitedHere : Bool
    reflectionPointAlignmentInhabitedHere : Bool
    unitCircleFixedPointInhabitedHere : Bool
    wolframJOver1728CalibrationCollapsedIntoStandardJ : Bool

open NormalizedAnalyticRendererBoundary public

canonicalNormalizedAnalyticRendererBoundary :
  NormalizedAnalyticRendererBoundary
canonicalNormalizedAnalyticRendererBoundary =
  normalized-analytic-renderer-boundary
    true true true true true true true
    false false false false
