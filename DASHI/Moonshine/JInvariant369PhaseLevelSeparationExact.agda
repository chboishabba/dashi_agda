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
-- 6. Consequence / firewall.
------------------------------------------------------------------------

record PhaseLevelSeparationBoundary : Set where
  constructor phase-level-separation-boundary
  field
    level3TranslationOrderThree : Bool
    level3TranslationFixedPointFree : Bool
    jPhaseInvariantUnderJPreservingModularAction : Bool
    phaseOnlyC3GloballyEqualsNontrivialLevel3Possible : Bool
    rendererStoredC3GloballyEqualsNontrivialLevel3Possible : Bool

    levelAwareSamePointFibreRequiredForPrincipalLevelReading : Bool
    canonicalLevel9And27RemainValidAsFibreObservers : Bool
    fixedLocusSixfoldToEisensteinC3Invalidated : Bool

open PhaseLevelSeparationBoundary public

canonicalPhaseLevelSeparationBoundary :
  PhaseLevelSeparationBoundary
canonicalPhaseLevelSeparationBoundary =
  phase-level-separation-boundary
    true true true
    false false
    true true false
