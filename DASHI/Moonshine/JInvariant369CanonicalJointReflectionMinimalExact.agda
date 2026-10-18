module DASHI.Moonshine.JInvariant369CanonicalJointReflectionMinimalExact where

------------------------------------------------------------------------
-- MINIMAL CANONICAL JOINT REFLECTION
--
-- The canonical fibred interpretation has:
--
--   phase lane: continuous phase -> C6 -> phase-C3
--   level lane: C27 -> C9 -> level-C3
--
-- Therefore phase-9 and phase-27 quantizers are NOT required to express the
-- canonical joint reflection architecture.  Those were artifacts of the older
-- all-in-one formulaic renderer interface.
--
-- This module constructs the reflection layer using only:
--
--   * the analytic normalized-j reflection point;
--   * continuous phase reflection;
--   * C6 phase-observer intertwining;
--   * the level-27 inversion law.
--
-- Phase-C3 reflection is then derived from the existing C6 -> C3 orientation
-- quotient.  Level-9 and level-3 reflection are derived from level-27 by the
-- canonical covering tower.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import Base369 as Base

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as Normalized
import DASHI.Moonshine.JSameWeightQuotientInvariantExact as J
import DASHI.Moonshine.JSameWeightQuotientReflectionExact as JRef
import DASHI.Moonshine.JInvariantAnalyticNormalizedKleinAdapterExact as Standard
import DASHI.Moonshine.JInvariant369NormalizedAnalyticRendererExact as Renderer

import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariant369ReflectionEquivarianceExact as Reflection
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact as Joint
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic

------------------------------------------------------------------------
-- 1. Minimal phase reflection interface.
------------------------------------------------------------------------

record CanonicalPhase6Reflection
    {M : Eisenstein.EisensteinAnalyticModel}
    {A : Disc.DiscriminantAlgebra M}
    {N : Normalized.WeightCompatibleNormalization M}
    {Q : J.QuotientCancellationAlgebra M}
    (O : Renderer.StandardJRendererReadout M)
    (AR : Standard.NormalizedJReflectionAlgebra M A N Q) : Set₁ where

  private
    R = Renderer.standardRenderer M A N Q O

  field
    reflectPhase :
      Render.Phase R → Render.Phase R

    phaseReflects :
      (tau : Eisenstein.Parameter M) →
      Render.jPhase R
        (JRef.reflectParameter
          (Standard.baseReflection AR)
          tau)
      ≡
      reflectPhase (Render.jPhase R tau)

    phase6Intertwines :
      (phase : Render.Phase R) →
      Render.phase6 R (reflectPhase phase)
      ≡
      Reflection.reflect6 (Render.phase6 R phase)

open CanonicalPhase6Reflection public

------------------------------------------------------------------------
-- 2. Minimal joint reflection action.
------------------------------------------------------------------------

record MinimalJointReflection
    {M : Eisenstein.EisensteinAnalyticModel}
    {A : Disc.DiscriminantAlgebra M}
    {N : Normalized.WeightCompatibleNormalization M}
    {Q : J.QuotientCancellationAlgebra M}
    (O : Renderer.StandardJRendererReadout M)
    (AR : Standard.NormalizedJReflectionAlgebra M A N Q)
    (L : Tower.CanonicalLevel27Lift
      (Renderer.standardRenderer M A N Q O)) : Set₁ where

  private
    R = Renderer.standardRenderer M A N Q O

  field
    phase :
      CanonicalPhase6Reflection O AR

    level27Reflects :
      (tau : Eisenstein.Parameter M) →
      Tower.level27At L
        (JRef.reflectParameter
          (Standard.baseReflection AR)
          tau)
      ≡
      Arithmetic.negateResidue
        (Tower.level27At L tau)

open MinimalJointReflection public

analyticReflectPoint :
  ∀ {M A N Q O AR L} →
  MinimalJointReflection
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L →
  Eisenstein.Parameter M →
  Eisenstein.Parameter M
analyticReflectPoint {AR = AR} W =
  JRef.reflectParameter (Standard.baseReflection AR)

------------------------------------------------------------------------
-- 3. C6 reflection theorem.
------------------------------------------------------------------------

minimalPhase6Reflects :
  ∀ {M A N Q O AR L} →
  (W : MinimalJointReflection
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  (tau : Eisenstein.Parameter M) →
  Render.phase6
    (Renderer.standardRenderer M A N Q O)
    (Render.jPhase
      (Renderer.standardRenderer M A N Q O)
      (analyticReflectPoint W tau))
  ≡
  Reflection.reflect6
    (Render.phase6
      (Renderer.standardRenderer M A N Q O)
      (Render.jPhase
        (Renderer.standardRenderer M A N Q O)
        tau))
minimalPhase6Reflects {M} {A} {N} {Q} {O} W tau =
  trans
    (cong
      (Render.phase6
        (Renderer.standardRenderer M A N Q O))
      (phaseReflects (phase W) tau))
    (phase6Intertwines
      (phase W)
      (Render.jPhase
        (Renderer.standardRenderer M A N Q O)
        tau))

------------------------------------------------------------------------
-- 4. Phase-C3 reflection is derived from C6.
------------------------------------------------------------------------

minimalPhaseC3Reflects :
  ∀ {M A N Q O AR L} →
  (W : MinimalJointReflection
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  (tau : Eisenstein.Parameter M) →
  Tower.level6To3
    (Render.phase6
      (Renderer.standardRenderer M A N Q O)
      (Render.jPhase
        (Renderer.standardRenderer M A N Q O)
        (analyticReflectPoint W tau)))
  ≡
  Arithmetic.negateResidue
    (Tower.level6To3
      (Render.phase6
        (Renderer.standardRenderer M A N Q O)
        (Render.jPhase
          (Renderer.standardRenderer M A N Q O)
          tau)))
minimalPhaseC3Reflects W tau =
  trans
    (cong Tower.level6To3
      (minimalPhase6Reflects W tau))
    (Joint.phase3ReflectionCommutesHex _)

------------------------------------------------------------------------
-- 5. Level tower reflection from the same analytic point.
------------------------------------------------------------------------

minimalLevel27ReflectionLift :
  ∀ {M A N Q O AR L} →
  (W : MinimalJointReflection
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  Tower.Level27ReflectionLift
    (Renderer.standardRenderer M A N Q O)
    L
minimalLevel27ReflectionLift {AR = AR} W =
  record
    { Tower.reflectPoint =
        JRef.reflectParameter
          (Standard.baseReflection AR)

    ; Tower.level27Reflection =
        level27Reflects W
    }

minimalLevel9Reflects :
  ∀ {M A N Q O AR L} →
  (W : MinimalJointReflection
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  (tau : Eisenstein.Parameter M) →
  Tower.canonicalLevel9At L
    (analyticReflectPoint W tau)
  ≡
  Arithmetic.negateResidue
    (Tower.canonicalLevel9At L tau)
minimalLevel9Reflects W =
  Tower.level9ReflectionDerived
    (minimalLevel27ReflectionLift W)

minimalLevel3Reflects :
  ∀ {M A N Q O AR L} →
  (W : MinimalJointReflection
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  (tau : Eisenstein.Parameter M) →
  Tower.canonicalLevel3At L
    (analyticReflectPoint W tau)
  ≡
  Arithmetic.negateResidue
    (Tower.canonicalLevel3At L tau)
minimalLevel3Reflects W =
  Tower.level3ReflectionDerived
    (minimalLevel27ReflectionLift W)

------------------------------------------------------------------------
-- 6. Standard j conjugation uses the same analytic reflection directly.
------------------------------------------------------------------------

minimalStandardJReflects :
  ∀ {M A N Q O AR L} →
  (W : MinimalJointReflection
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  (tau : Eisenstein.Parameter M) →
  Render.jValue
    (Renderer.standardRenderer M A N Q O)
    (analyticReflectPoint W tau)
  ≡
  JRef.conjugate (Standard.baseReflection AR)
    (Render.jValue
      (Renderer.standardRenderer M A N Q O)
      tau)
minimalStandardJReflects {M} {A} {N} {Q} {O} {AR} W tau =
  Standard.standardJReflects AR tau

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

record MinimalCanonicalReflectionBoundary : Set where
  constructor minimal-canonical-reflection-boundary
  field
    continuousPhaseReflectionRequired : Bool
    phaseC6IntertwinerRequired : Bool
    phaseC3DerivedFromC6 : Bool
    phaseC9QuantizerRequiredForCanonicalBundle : Bool
    phaseC27QuantizerRequiredForCanonicalBundle : Bool

    level27ReflectionRequired : Bool
    level9ReflectionDerivedFrom27 : Bool
    level3ReflectionDerivedFrom27 : Bool

    analyticReflectionPointSharedDefinitionally : Bool
    standardJConjugationDerivedDirectly : Bool

canonicalMinimalCanonicalReflectionBoundary :
  MinimalCanonicalReflectionBoundary
canonicalMinimalCanonicalReflectionBoundary =
  minimal-canonical-reflection-boundary
    true true true false false
    true true true
    true true
