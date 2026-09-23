module DASHI.Moonshine.JInvariant369NormalizedRendererCanonicalReflectionExact where

------------------------------------------------------------------------
-- CANONICAL NORMALIZED-j REFLECTION COMPILER
--
-- The normalized renderer already has the correct analytic point/value carrier
-- by definition.  Previously the joint reflection layer still asked for an
-- independent proof that its reflected point agreed with the analytic
-- normalized-j reflection.
--
-- This module removes that duplication.
--
-- Choose the analytic reflection point ONCE:
--
--   r(tau) = JRef.reflectParameter(baseReflection AR, tau).
--
-- Then supply only:
--
--   * continuous phase reflection under r;
--   * finite C3/C6/C9/C27 observer intertwiners;
--   * the level-27 inversion law under r.
--
-- The phase reflection lift, level reflection lift, joint reflection action,
-- and normalized-renderer reflection alignment are all constructed using the
-- same point function.  Their alignment equations are therefore refl.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as Normalized
import DASHI.Moonshine.JSameWeightQuotientInvariantExact as J
import DASHI.Moonshine.JSameWeightQuotientReflectionExact as JRef
import DASHI.Moonshine.JInvariantAnalyticNormalizedKleinAdapterExact as Standard
import DASHI.Moonshine.JInvariant369NormalizedAnalyticRendererExact as NormalizedRenderer

import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariant369ReflectionEquivarianceExact as Reflection
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact as Joint
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic

------------------------------------------------------------------------
-- 1. One analytic-point reflection package.
------------------------------------------------------------------------

record CanonicalNormalizedReflectionInputs
    {M : Eisenstein.EisensteinAnalyticModel}
    {A : Disc.DiscriminantAlgebra M}
    {N : Normalized.WeightCompatibleNormalization M}
    {Q : J.QuotientCancellationAlgebra M}
    (O : NormalizedRenderer.StandardJRendererReadout M)
    (AR : Standard.NormalizedJReflectionAlgebra M A N Q)
    (L : Tower.CanonicalLevel27Lift
      (NormalizedRenderer.standardRenderer M A N Q O)) : Set₁ where

  private
    R = NormalizedRenderer.standardRenderer M A N Q O

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

    observer3Intertwines :
      (phase : Render.Phase R) →
      Render.phase3 R (reflectPhase phase)
      ≡
      Reflection.reflect3 (Render.phase3 R phase)

    observer6Intertwines :
      (phase : Render.Phase R) →
      Render.phase6 R (reflectPhase phase)
      ≡
      Reflection.reflect6 (Render.phase6 R phase)

    observer9Intertwines :
      (phase : Render.Phase R) →
      Render.phase9 R (reflectPhase phase)
      ≡
      Reflection.reflect9 (Render.phase9 R phase)

    observer27Intertwines :
      (phase : Render.Phase R) →
      Render.phase27 R (reflectPhase phase)
      ≡
      Reflection.reflect27 (Render.phase27 R phase)

    level27Reflects :
      (tau : Eisenstein.Parameter M) →
      Tower.level27At L
        (JRef.reflectParameter
          (Standard.baseReflection AR)
          tau)
      ≡
      Arithmetic.negateResidue
        (Tower.level27At L tau)

open CanonicalNormalizedReflectionInputs public

------------------------------------------------------------------------
-- 2. Phase reflection with the analytic point map by construction.
------------------------------------------------------------------------

canonicalPhaseReflection :
  ∀ {M A N Q O AR L} →
  CanonicalNormalizedReflectionInputs
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L →
  Reflection.J369ReflectionEquivariance
    (NormalizedRenderer.standardRenderer M A N Q O)
canonicalPhaseReflection {AR = AR} I =
  record
    { Reflection.reflectPoint =
        JRef.reflectParameter
          (Standard.baseReflection AR)

    ; Reflection.reflectPhase =
        reflectPhase I

    ; Reflection.phaseReflection =
        phaseReflects I

    ; Reflection.observer3Intertwines =
        observer3Intertwines I

    ; Reflection.observer6Intertwines =
        observer6Intertwines I

    ; Reflection.observer9Intertwines =
        observer9Intertwines I

    ; Reflection.observer27Intertwines =
        observer27Intertwines I
    }

------------------------------------------------------------------------
-- 3. Level reflection uses the SAME analytic point map.
------------------------------------------------------------------------

canonicalLevelReflection :
  ∀ {M A N Q O AR L} →
  (I : CanonicalNormalizedReflectionInputs
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  Tower.Level27ReflectionLift
    (NormalizedRenderer.standardRenderer M A N Q O)
    L
canonicalLevelReflection {AR = AR} I =
  record
    { Tower.reflectPoint =
        JRef.reflectParameter
          (Standard.baseReflection AR)

    ; Tower.level27Reflection =
        level27Reflects I
    }

------------------------------------------------------------------------
-- 4. Joint reflection alignment is now definitional.
------------------------------------------------------------------------

canonicalJointReflection :
  ∀ {M A N Q O AR L} →
  (I : CanonicalNormalizedReflectionInputs
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  Joint.JointReflectionAction
    (NormalizedRenderer.standardRenderer M A N Q O)
    L
canonicalJointReflection I =
  record
    { Joint.phaseReflection =
        canonicalPhaseReflection I

    ; Joint.levelReflection =
        canonicalLevelReflection I

    ; Joint.sameReflectedPoint =
        λ tau → refl
    }

canonicalNormalizedRendererAlignment :
  ∀ {M A N Q O AR L} →
  (I : CanonicalNormalizedReflectionInputs
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  NormalizedRenderer.NormalizedRendererReflectionAlignment
    {M = M} {A = A} {N = N} {Q = Q}
    O AR {L = L}
    (canonicalJointReflection I)
canonicalNormalizedRendererAlignment I =
  record
    { NormalizedRenderer.reflectionPointAgrees =
        λ tau → refl
    }

------------------------------------------------------------------------
-- 5. Therefore standard-j conjugation enters the joint bundle automatically.
------------------------------------------------------------------------

canonicalJointJConjugation :
  ∀ {M A N Q O AR L} →
  (I : CanonicalNormalizedReflectionInputs
    {M = M} {A = A} {N = N} {Q = Q}
    O AR L) →
  Joint.JointJConjugation
    (canonicalJointReflection I)
canonicalJointJConjugation I =
  NormalizedRenderer.jointJConjugationFromNormalizedRenderer
    (canonicalNormalizedRendererAlignment I)

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

record CanonicalNormalizedReflectionBoundary : Set where
  constructor canonical-normalized-reflection-boundary
  field
    analyticReflectionPointSelectedOnce : Bool
    phaseReflectionLiftCompilerOwned : Bool
    levelReflectionLiftCompilerOwned : Bool
    jointReflectionCompilerOwned : Bool
    jointSamePointAlignmentIsDefinitional : Bool
    normalizedRendererPointAlignmentIsDefinitional : Bool
    jointJConjugationCompilerOwned : Bool

    continuousPhaseReflectionIntertwinerInhabitedHere : Bool
    finiteObserverIntertwinersInhabitedHere : Bool
    level27AnalyticReflectionLawInhabitedHere : Bool

canonicalCanonicalNormalizedReflectionBoundary :
  CanonicalNormalizedReflectionBoundary
canonicalCanonicalNormalizedReflectionBoundary =
  canonical-normalized-reflection-boundary
    true true true true true true true
    false false false
