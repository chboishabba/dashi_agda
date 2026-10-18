module DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact where

------------------------------------------------------------------------
-- PHASE-ONLY OBSERVER != NONTRIVIAL PRINCIPAL-LEVEL CUSP COORDINATE
--
-- This is the decisive anti-overclaim theorem for the 369 observer story.
--
-- Existing facts:
--
--   * JInvariantFormulaic369ModularReplicationExact:
--       if a modular action preserves j, then jPhase and every observer that is
--       only a function of jPhase are invariant.
--
--   * JInvariant369CanonicalLevelObserverTowerExact:
--       the genuine level-3 cusp coordinate carries an order-three translation
--       action with no fixed point.
--
-- Therefore a globally phase-only C3 observer cannot simultaneously be the
-- genuine nontrivial level-3 cusp coordinate under T.
--
-- This does NOT invalidate the level tower.  It identifies the correct object:
-- level 3/9/27 live in the same-point modular fibre over j, not in jPhase alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (neg; zer; pos; []; _∷_)

import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369ModularReplicationExact as Replication
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Canonical
import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric

------------------------------------------------------------------------
-- 1. The genuine level-3 translation has no fixed point.
------------------------------------------------------------------------

data Empty : Set where

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → Empty

level3TranslationNoFixedPoint :
  (x : Level.level3CuspFibre) →
  Canonical.translateLevel3Residue x ≢ x
level3TranslationNoFixedPoint (neg ∷ []) ()
level3TranslationNoFixedPoint (zer ∷ []) ()
level3TranslationNoFixedPoint (pos ∷ []) ()

level9TranslationNoFixedPoint :
  (x : Level.level9CuspFibre) →
  Level.translateTriadic Q.two x ≢ x
level9TranslationNoFixedPoint x fixed =
  level3TranslationNoFixedPoint
    (Level.level9To3CoveringProjection x)
    (trans
      (sym (Level.level9To3TranslationEquivariant x))
      (cong Level.level9To3CoveringProjection fixed))

level27TranslationNoFixedPoint :
  (x : Level.level27CuspFibre) →
  Level.translateTriadic Q.three x ≢ x
level27TranslationNoFixedPoint x fixed =
  level9TranslationNoFixedPoint
    (Level.level27To9CoveringProjection x)
    (trans
      (sym (Level.level27To9TranslationEquivariant x))
      (cong Level.level27To9CoveringProjection fixed))

------------------------------------------------------------------------
-- 2. A T-action on points that preserves j but translates the level fibre.
------------------------------------------------------------------------

record PhaseLevel3TranslationAttempt
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (L : Canonical.CanonicalLevel27Lift R) : Set₁ where
  field
    translationMatrix : Replication.Matrix A

    actsAsLevelTranslation :
      (z : Klein.Point (Render.klein R)) →
      Canonical.canonicalLevel3At L
        (Replication.act A translationMatrix z)
      ≡
      Canonical.translateLevel3Residue
        (Canonical.canonicalLevel3At L z)

    phase3AgreesWithLevel3 :
      (z : Klein.Point (Render.klein R)) →
      Level.observer3ToLevel3
        (Render.phase3 R (Render.jPhase R z))
      ≡
      Canonical.canonicalLevel3At L z

open PhaseLevel3TranslationAttempt public

------------------------------------------------------------------------
-- 3. Phase-only invariance forces the alleged level coordinate to be fixed.
------------------------------------------------------------------------

phaseOnlyCalibrationForcesLevel3Fixed :
  ∀ {R A L} →
  (W : PhaseLevel3TranslationAttempt R A L) →
  (z : Klein.Point (Render.klein R)) →
  Canonical.translateLevel3Residue
    (Canonical.canonicalLevel3At L z)
  ≡
  Canonical.canonicalLevel3At L z
phaseOnlyCalibrationForcesLevel3Fixed {R} {A} {L} W z =
  trans
    (sym (actsAsLevelTranslation W z))
    (trans
      (sym (phase3AgreesWithLevel3 W
        (Replication.act A (translationMatrix W) z)))
      (trans
        (cong Level.observer3ToLevel3
          (cong (Render.phase3 R)
            (Replication.phaseInvariant
              R A (translationMatrix W) z)))
        (phase3AgreesWithLevel3 W z)))

------------------------------------------------------------------------
-- 4. No-go: there is no such global phase-only calibration.
------------------------------------------------------------------------

phaseOnlyC3CannotBeNontrivialLevel3 :
  ∀ {R A L} →
  PhaseLevel3TranslationAttempt R A L →
  (z : Klein.Point (Render.klein R)) →
  Empty
phaseOnlyC3CannotBeNontrivialLevel3 {L = L} W z =
  level3TranslationNoFixedPoint
    (Canonical.canonicalLevel3At L z)
    (phaseOnlyCalibrationForcesLevel3Fixed W z)

------------------------------------------------------------------------
-- 5. Equivalent formulation using the renderer's actual stored C3 sample.
------------------------------------------------------------------------

record RenderSampleLevel3TranslationAttempt
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (L : Canonical.CanonicalLevel27Lift R) : Set₁ where
  field
    translationMatrix : Replication.Matrix A

    actsAsLevelTranslation :
      (z : Klein.Point (Render.klein R)) →
      Canonical.canonicalLevel3At L
        (Replication.act A translationMatrix z)
      ≡
      Canonical.translateLevel3Residue
        (Canonical.canonicalLevel3At L z)

    rendererC3AgreesWithLevel3 :
      (z : Klein.Point (Render.klein R)) →
      Level.observer3ToLevel3
        (Render.observer3 (Render.renderAt R z))
      ≡
      Canonical.canonicalLevel3At L z

open RenderSampleLevel3TranslationAttempt public

renderSampleCalibrationForcesFixed :
  ∀ {R A L} →
  (W : RenderSampleLevel3TranslationAttempt R A L) →
  (z : Klein.Point (Render.klein R)) →
  Canonical.translateLevel3Residue
    (Canonical.canonicalLevel3At L z)
  ≡
  Canonical.canonicalLevel3At L z
renderSampleCalibrationForcesFixed {R} {A} {L} W z =
  trans
    (sym (RenderSampleLevel3TranslationAttempt.actsAsLevelTranslation W z))
    (trans
      (sym
        (rendererC3AgreesWithLevel3 W
          (Replication.act A
            (RenderSampleLevel3TranslationAttempt.translationMatrix W)
            z)))
      (trans
        (cong Level.observer3ToLevel3
          (Replication.observer3Invariant
            R A
            (RenderSampleLevel3TranslationAttempt.translationMatrix W)
            z))
        (rendererC3AgreesWithLevel3 W z)))

renderSampleC3CannotBeNontrivialLevel3 :
  ∀ {R A L} →
  RenderSampleLevel3TranslationAttempt R A L →
  (z : Klein.Point (Render.klein R)) →
  Empty
renderSampleC3CannotBeNontrivialLevel3 {L = L} W z =
  level3TranslationNoFixedPoint
    (Canonical.canonicalLevel3At L z)
    (renderSampleCalibrationForcesFixed W z)

------------------------------------------------------------------------
-- 6. The same separation holds for the legacy phase-only 9/27 observers.
------------------------------------------------------------------------

record PhaseLevel9TranslationAttempt
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (L : Canonical.CanonicalLevel27Lift R) : Set₁ where
  field
    translationMatrix : Replication.Matrix A

    actsAsLevelTranslation :
      (z : Klein.Point (Render.klein R)) →
      Canonical.canonicalLevel9At L
        (Replication.act A translationMatrix z)
      ≡
      Level.translateTriadic Q.two
        (Canonical.canonicalLevel9At L z)

    phase9AgreesWithLevel9 :
      (z : Klein.Point (Render.klein R)) →
      Level.observer9ToLevel9
        (Render.phase9 R (Render.jPhase R z))
      ≡
      Canonical.canonicalLevel9At L z

open PhaseLevel9TranslationAttempt public

phaseOnly9CalibrationForcesFixed :
  ∀ {R A L} →
  (W : PhaseLevel9TranslationAttempt R A L) →
  (z : Klein.Point (Render.klein R)) →
  Level.translateTriadic Q.two
    (Canonical.canonicalLevel9At L z)
  ≡
  Canonical.canonicalLevel9At L z
phaseOnly9CalibrationForcesFixed {R} {A} {L} W z =
  trans
    (sym (PhaseLevel9TranslationAttempt.actsAsLevelTranslation W z))
    (trans
      (sym
        (phase9AgreesWithLevel9 W
          (Replication.act A
            (PhaseLevel9TranslationAttempt.translationMatrix W)
            z)))
      (trans
        (cong Level.observer9ToLevel9
          (cong (Render.phase9 R)
            (Replication.phaseInvariant
              R A
              (PhaseLevel9TranslationAttempt.translationMatrix W)
              z)))
        (phase9AgreesWithLevel9 W z)))

phaseOnly9CannotBeNontrivialLevel9 :
  ∀ {R A L} →
  PhaseLevel9TranslationAttempt R A L →
  (z : Klein.Point (Render.klein R)) →
  Empty
phaseOnly9CannotBeNontrivialLevel9 {L = L} W z =
  level9TranslationNoFixedPoint
    (Canonical.canonicalLevel9At L z)
    (phaseOnly9CalibrationForcesFixed W z)

record PhaseLevel27TranslationAttempt
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (L : Canonical.CanonicalLevel27Lift R) : Set₁ where
  field
    translationMatrix : Replication.Matrix A

    actsAsLevelTranslation :
      (z : Klein.Point (Render.klein R)) →
      Canonical.level27At L
        (Replication.act A translationMatrix z)
      ≡
      Level.translateTriadic Q.three
        (Canonical.level27At L z)

    phase27AgreesWithLevel27 :
      (z : Klein.Point (Render.klein R)) →
      Level.observer27ToLevel27
        (Render.phase27 R (Render.jPhase R z))
      ≡
      Canonical.level27At L z

open PhaseLevel27TranslationAttempt public

phaseOnly27CalibrationForcesFixed :
  ∀ {R A L} →
  (W : PhaseLevel27TranslationAttempt R A L) →
  (z : Klein.Point (Render.klein R)) →
  Level.translateTriadic Q.three
    (Canonical.level27At L z)
  ≡
  Canonical.level27At L z
phaseOnly27CalibrationForcesFixed {R} {A} {L} W z =
  trans
    (sym (PhaseLevel27TranslationAttempt.actsAsLevelTranslation W z))
    (trans
      (sym
        (phase27AgreesWithLevel27 W
          (Replication.act A
            (PhaseLevel27TranslationAttempt.translationMatrix W)
            z)))
      (trans
        (cong Level.observer27ToLevel27
          (cong (Render.phase27 R)
            (Replication.phaseInvariant
              R A
              (PhaseLevel27TranslationAttempt.translationMatrix W)
              z)))
        (phase27AgreesWithLevel27 W z)))

phaseOnly27CannotBeNontrivialLevel27 :
  ∀ {R A L} →
  PhaseLevel27TranslationAttempt R A L →
  (z : Klein.Point (Render.klein R)) →
  Empty
phaseOnly27CannotBeNontrivialLevel27 {L = L} W z =
  level27TranslationNoFixedPoint
    (Canonical.level27At L z)
    (phaseOnly27CalibrationForcesFixed W z)

------------------------------------------------------------------------
-- 6. Consequence / firewall.
------------------------------------------------------------------------

record PhaseLevelSeparationBoundary : Set where
  constructor phase-level-separation-boundary
  field
    level3TranslationOrderThree : Bool
    level3TranslationFixedPointFree : Bool
    level9TranslationFixedPointFree : Bool
    level27TranslationFixedPointFree : Bool
    jPhaseInvariantUnderJPreservingModularAction : Bool
    phaseOnlyC3GloballyEqualsNontrivialLevel3Possible : Bool
    rendererStoredC3GloballyEqualsNontrivialLevel3Possible : Bool
    phaseOnly9GloballyEqualsNontrivialLevel9Possible : Bool
    phaseOnly27GloballyEqualsNontrivialLevel27Possible : Bool

    levelAwareSamePointFibreRequiredForPrincipalLevelReading : Bool
    canonicalLevel9And27RemainValidAsFibreObservers : Bool
    fixedLocusSixfoldToEisensteinC3Invalidated : Bool

open PhaseLevelSeparationBoundary public

canonicalPhaseLevelSeparationBoundary :
  PhaseLevelSeparationBoundary
canonicalPhaseLevelSeparationBoundary =
  phase-level-separation-boundary
    true true true true true
    false false false false
    true true false
