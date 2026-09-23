module DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact where

------------------------------------------------------------------------
-- JOINT J / PHASE / PRINCIPAL-LEVEL FIBRE
--
-- The phase and level lanes both contain three-state carriers, but they have
-- different transformation laws.  This module makes that distinction
-- type-visible.
--
--   phase C3:
--     obtained from the genuine C6 phase/reflection state by forgetting its
--     C2 orientation coordinate.
--
--   level C3:
--     obtained from a genuine principal-level C27 lift by the canonical
--     C27 -> C9 -> C3 covering projections.
--
-- Under a j-preserving T-action:
--
--   j, continuous phase, C6 phase, phase-C3     stay fixed;
--   level-C27, level-C9, level-C3              translate.
--
-- Hence the two C3 roles cannot be silently identified.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

import Base369 as Base
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369ModularReplicationExact as Replication
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Separation
import DASHI.Foundations.TriadicFiniteQuotient as Q

------------------------------------------------------------------------
-- 1. Role wrappers.
------------------------------------------------------------------------

record PhaseC3 : Set where
  constructor phase-c3
  field
    phaseResidue : Level.level3CuspFibre

record LevelC3 : Set where
  constructor level-c3
  field
    levelResidue3 : Level.level3CuspFibre

record LevelC9 : Set where
  constructor level-c9
  field
    levelResidue9 : Level.level9CuspFibre

record LevelC27 : Set where
  constructor level-c27
  field
    levelResidue27 : Level.level27CuspFibre

open PhaseC3 public
open LevelC3 public
open LevelC9 public
open LevelC27 public

------------------------------------------------------------------------
-- 2. Joint sample.
------------------------------------------------------------------------

record JLevel27Sample
    (R : Render.JPhaseRenderingAlgebra)
    (L : Tower.CanonicalLevel27Lift R) : Set where
  constructor j-level27-sample
  field
    point : Klein.Point (Render.klein R)

    exactJ : Klein.Value (Render.klein R)
    exactPhase : Render.Phase R

    phase6State : Base.HexTruth
    phase3State : PhaseC3

    level27State : LevelC27
    level9State : LevelC9
    level3State : LevelC3

open JLevel27Sample public

sampleAt :
  ∀ {R} →
  (L : Tower.CanonicalLevel27Lift R) →
  Klein.Point (Render.klein R) →
  JLevel27Sample R L
sampleAt {R} L z =
  j-level27-sample
    z
    (Render.jValue R z)
    (Render.jPhase R z)
    (Render.phase6 R (Render.jPhase R z))
    (phase-c3
      (Tower.level6To3
        (Render.phase6 R (Render.jPhase R z))))
    (level-c27 (Tower.level27At L z))
    (level-c9 (Tower.canonicalLevel9At L z))
    (level-c3 (Tower.canonicalLevel3At L z))

------------------------------------------------------------------------
-- 3. Exact retention/projection theorems.
------------------------------------------------------------------------

sampleRetainsJ :
  ∀ {R L} (z : Klein.Point (Render.klein R)) →
  exactJ (sampleAt L z) ≡ Render.jValue R z
sampleRetainsJ z = refl

sampleRetainsPhase :
  ∀ {R L} (z : Klein.Point (Render.klein R)) →
  exactPhase (sampleAt L z) ≡ Render.jPhase R z
sampleRetainsPhase z = refl

phase3IsOrientationQuotient :
  ∀ {R L} (z : Klein.Point (Render.klein R)) →
  phaseResidue (phase3State (sampleAt L z))
  ≡
  Tower.level6To3
    (phase6State (sampleAt L z))
phase3IsOrientationQuotient z = refl

level27DeterminesLevel9 :
  ∀ {R L} (z : Klein.Point (Render.klein R)) →
  levelResidue9 (level9State (sampleAt L z))
  ≡
  Level.level27To9CoveringProjection
    (levelResidue27 (level27State (sampleAt L z)))
level27DeterminesLevel9 z = refl

level9DeterminesLevel3 :
  ∀ {R L} (z : Klein.Point (Render.klein R)) →
  levelResidue3 (level3State (sampleAt L z))
  ≡
  Level.level9To3CoveringProjection
    (levelResidue9 (level9State (sampleAt L z)))
level9DeterminesLevel3 z = refl

------------------------------------------------------------------------
-- 4. Joint T-action.
--
-- The same point action is required to be both:
--   * j-preserving for the renderer;
--   * translation by one on the genuine level-27 fibre.
------------------------------------------------------------------------

record JointTAction
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (L : Tower.CanonicalLevel27Lift R) : Set₁ where
  field
    T : Replication.Matrix A

    level27Translates :
      (z : Klein.Point (Render.klein R)) →
      Tower.level27At L (Replication.act A T z)
      ≡
      Level.translateTriadic Q.three
        (Tower.level27At L z)

open JointTAction public

asLevel27TranslationLift :
  ∀ {R A L} →
  JointTAction R A L →
  Tower.Level27TranslationLift R L
asLevel27TranslationLift {A = A} W =
  record
    { Tower.translatePoint = Replication.act A (T W)
    ; Tower.level27Translation = level27Translates W
    }

------------------------------------------------------------------------
-- 5. T fixes j and phase data.
------------------------------------------------------------------------

jointTJInvariant :
  ∀ {R A L} →
  (W : JointTAction R A L) →
  (z : Klein.Point (Render.klein R)) →
  exactJ (sampleAt L (Replication.act A (T W) z))
  ≡
  exactJ (sampleAt L z)
jointTJInvariant {R} {A} W z =
  Replication.jInvariant A (T W) z

jointTPhaseInvariant :
  ∀ {R A L} →
  (W : JointTAction R A L) →
  (z : Klein.Point (Render.klein R)) →
  exactPhase (sampleAt L (Replication.act A (T W) z))
  ≡
  exactPhase (sampleAt L z)
jointTPhaseInvariant {R} {A} W z =
  Replication.phaseInvariant R A (T W) z

jointTPhase6Invariant :
  ∀ {R A L} →
  (W : JointTAction R A L) →
  (z : Klein.Point (Render.klein R)) →
  phase6State (sampleAt L (Replication.act A (T W) z))
  ≡
  phase6State (sampleAt L z)
jointTPhase6Invariant {R} {A} W z =
  cong (Render.phase6 R)
    (Replication.phaseInvariant R A (T W) z)

jointTPhase3Invariant :
  ∀ {R A L} →
  (W : JointTAction R A L) →
  (z : Klein.Point (Render.klein R)) →
  phase3State (sampleAt L (Replication.act A (T W) z))
  ≡
  phase3State (sampleAt L z)
jointTPhase3Invariant W z =
  cong phase-c3
    (cong Tower.level6To3
      (jointTPhase6Invariant W z))

------------------------------------------------------------------------
-- 6. T translates the genuine level tower.
------------------------------------------------------------------------

jointTLevel27Translates :
  ∀ {R A L} →
  (W : JointTAction R A L) →
  (z : Klein.Point (Render.klein R)) →
  levelResidue27
    (level27State (sampleAt L (Replication.act A (T W) z)))
  ≡
  Level.translateTriadic Q.three
    (levelResidue27 (level27State (sampleAt L z)))
jointTLevel27Translates W z =
  level27Translates W z

jointTLevel9Translates :
  ∀ {R A L} →
  (W : JointTAction R A L) →
  (z : Klein.Point (Render.klein R)) →
  levelResidue9
    (level9State (sampleAt L (Replication.act A (T W) z)))
  ≡
  Level.translateTriadic Q.two
    (levelResidue9 (level9State (sampleAt L z)))
jointTLevel9Translates W z =
  Tower.level9TranslationDerived
    (asLevel27TranslationLift W) z

jointTLevel3Translates :
  ∀ {R A L} →
  (W : JointTAction R A L) →
  (z : Klein.Point (Render.klein R)) →
  levelResidue3
    (level3State (sampleAt L (Replication.act A (T W) z)))
  ≡
  Level.translateTriadic Q.one
    (levelResidue3 (level3State (sampleAt L z)))
jointTLevel3Translates W z =
  Tower.level3TranslationDerived
    (asLevel27TranslationLift W) z

------------------------------------------------------------------------
-- 7. Constructive separation of the two C3 roles.
--
-- If one postulates pointwise equality between phase-C3 and level-C3 while
-- using this same T-action, the phase side is fixed and the level side moves.
-- The existing no-fixed-point theorem then gives a contradiction.
------------------------------------------------------------------------

record PhaseEqualsLevel3UnderT
    {R : Render.JPhaseRenderingAlgebra}
    {A : Replication.J369ModularAction R}
    {L : Tower.CanonicalLevel27Lift R}
    (W : JointTAction R A L) : Set₁ where
  field
    sameC3 :
      (z : Klein.Point (Render.klein R)) →
      phaseResidue (phase3State (sampleAt L z))
      ≡
      levelResidue3 (level3State (sampleAt L z))

open PhaseEqualsLevel3UnderT public

phaseAndLevelC3CannotBeGloballyIdentified :
  ∀ {R A L}
    {W : JointTAction R A L} →
  PhaseEqualsLevel3UnderT W →
  (z : Klein.Point (Render.klein R)) →
  Separation.Empty
phaseAndLevelC3CannotBeGloballyIdentified {L = L} {W = W} E z =
  Separation.level3TranslationNoFixedPoint
    (Tower.canonicalLevel3At L z)
    fixed
  where
  fixed :
    Level.translateTriadic Q.one
      (Tower.canonicalLevel3At L z)
    ≡
    Tower.canonicalLevel3At L z
  fixed =
    begin
      Level.translateTriadic Q.one
        (Tower.canonicalLevel3At L z)
        ≡⟨ sym (jointTLevel3Translates W z) ⟩
      Tower.canonicalLevel3At L
        (Replication.act _ (T W) z)
        ≡⟨ sym (sameC3 E (Replication.act _ (T W) z)) ⟩
      phaseResidue
        (phase3State
          (sampleAt L (Replication.act _ (T W) z)))
        ≡⟨ cong phaseResidue (jointTPhase3Invariant W z) ⟩
      phaseResidue (phase3State (sampleAt L z))
        ≡⟨ sameC3 E z ⟩
      Tower.canonicalLevel3At L z
    ∎

------------------------------------------------------------------------
-- 8. Boundary.
------------------------------------------------------------------------

record JointPhaseLevelBoundary : Set where
  constructor joint-phase-level-boundary
  field
    jointJPhaseLevelSampleOwned : Bool
    phaseC3RoleTypeDistinctFromLevelC3Role : Bool
    phaseC3DerivedFromC6OrientationQuotient : Bool
    levelC3DerivedFromC27ViaC9 : Bool

    tFixesJ : Bool
    tFixesContinuousPhase : Bool
    tFixesPhaseC6 : Bool
    tFixesPhaseC3 : Bool
    tTranslatesLevelC27 : Bool
    tTranslatesLevelC9 : Bool
    tTranslatesLevelC3 : Bool

    globalPhaseC3EqualsLevelC3CompatibleWithT : Bool
    fullDeckGroupCollapsedToC27 : Bool

open JointPhaseLevelBoundary public

canonicalJointPhaseLevelBoundary : JointPhaseLevelBoundary
canonicalJointPhaseLevelBoundary =
  joint-phase-level-boundary
    true true true true
    true true true true
    true true true
    false false
