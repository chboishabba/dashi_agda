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
  using (_≡_; refl; cong; sym)

import Base369 as Base
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369ModularReplicationExact as Replication
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Separation
import DASHI.Moonshine.JInvariant369ReflectionEquivarianceExact as Reflection
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic

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
-- 8. Joint reflection action.
--
-- The renderer reflection and principal-level reflection must describe the
-- same reflected analytic point.  Once aligned, the finite action table is
-- derived rather than postulated.
------------------------------------------------------------------------

phase3ReflectionCommutesHex :
  (x : Base.HexTruth) →
  Tower.level6To3 (Reflection.reflect6 x)
  ≡
  Arithmetic.negateResidue (Tower.level6To3 x)
phase3ReflectionCommutesHex Base.hex-0 = refl
phase3ReflectionCommutesHex Base.hex-1 = refl
phase3ReflectionCommutesHex Base.hex-2 = refl
phase3ReflectionCommutesHex Base.hex-3 = refl
phase3ReflectionCommutesHex Base.hex-4 = refl
phase3ReflectionCommutesHex Base.hex-5 = refl

record JointReflectionAction
    (R : Render.JPhaseRenderingAlgebra)
    (L : Tower.CanonicalLevel27Lift R) : Set₁ where
  field
    phaseReflection : Reflection.J369ReflectionEquivariance R
    levelReflection : Tower.Level27ReflectionLift R L

    sameReflectedPoint :
      (z : Klein.Point (Render.klein R)) →
      Reflection.reflectPoint phaseReflection z
      ≡
      Tower.reflectPoint levelReflection z

open JointReflectionAction public

jointRPhase6Reflects :
  ∀ {R L} →
  (W : JointReflectionAction R L) →
  (z : Klein.Point (Render.klein R)) →
  phase6State
    (sampleAt L
      (Reflection.reflectPoint (phaseReflection W) z))
  ≡
  Reflection.reflect6 (phase6State (sampleAt L z))
jointRPhase6Reflects {R} W z =
  Reflection.observer6ReflectionCommutes
    R (phaseReflection W) z

jointRPhase3Reflects :
  ∀ {R L} →
  (W : JointReflectionAction R L) →
  (z : Klein.Point (Render.klein R)) →
  phaseResidue
    (phase3State
      (sampleAt L
        (Reflection.reflectPoint (phaseReflection W) z)))
  ≡
  Arithmetic.negateResidue
    (phaseResidue (phase3State (sampleAt L z)))
jointRPhase3Reflects W z =
  begin
    phaseResidue
      (phase3State
        (sampleAt _
          (Reflection.reflectPoint (phaseReflection W) z)))
      ≡⟨ cong Tower.level6To3 (jointRPhase6Reflects W z) ⟩
    Tower.level6To3
      (Reflection.reflect6 (phase6State (sampleAt _ z)))
      ≡⟨ phase3ReflectionCommutesHex
            (phase6State (sampleAt _ z)) ⟩
    Arithmetic.negateResidue
      (phaseResidue (phase3State (sampleAt _ z)))
  ∎

jointRLevel27Reflects :
  ∀ {R L} →
  (W : JointReflectionAction R L) →
  (z : Klein.Point (Render.klein R)) →
  levelResidue27
    (level27State
      (sampleAt L
        (Reflection.reflectPoint (phaseReflection W) z)))
  ≡
  Arithmetic.negateResidue
    (levelResidue27 (level27State (sampleAt L z)))
jointRLevel27Reflects {L = L} W z =
  begin
    Tower.level27At L
      (Reflection.reflectPoint (phaseReflection W) z)
      ≡⟨ cong (Tower.level27At L) (sameReflectedPoint W z) ⟩
    Tower.level27At L
      (Tower.reflectPoint (levelReflection W) z)
      ≡⟨ Tower.level27Reflection (levelReflection W) z ⟩
    Arithmetic.negateResidue (Tower.level27At L z)
  ∎

jointRLevel9Reflects :
  ∀ {R L} →
  (W : JointReflectionAction R L) →
  (z : Klein.Point (Render.klein R)) →
  levelResidue9
    (level9State
      (sampleAt L
        (Reflection.reflectPoint (phaseReflection W) z)))
  ≡
  Arithmetic.negateResidue
    (levelResidue9 (level9State (sampleAt L z)))
jointRLevel9Reflects {L = L} W z =
  begin
    Tower.canonicalLevel9At L
      (Reflection.reflectPoint (phaseReflection W) z)
      ≡⟨ cong (Tower.canonicalLevel9At L) (sameReflectedPoint W z) ⟩
    Tower.canonicalLevel9At L
      (Tower.reflectPoint (levelReflection W) z)
      ≡⟨ Tower.level9ReflectionDerived (levelReflection W) z ⟩
    Arithmetic.negateResidue (Tower.canonicalLevel9At L z)
  ∎

jointRLevel3Reflects :
  ∀ {R L} →
  (W : JointReflectionAction R L) →
  (z : Klein.Point (Render.klein R)) →
  levelResidue3
    (level3State
      (sampleAt L
        (Reflection.reflectPoint (phaseReflection W) z)))
  ≡
  Arithmetic.negateResidue
    (levelResidue3 (level3State (sampleAt L z)))
jointRLevel3Reflects {L = L} W z =
  begin
    Tower.canonicalLevel3At L
      (Reflection.reflectPoint (phaseReflection W) z)
      ≡⟨ cong (Tower.canonicalLevel3At L) (sameReflectedPoint W z) ⟩
    Tower.canonicalLevel3At L
      (Tower.reflectPoint (levelReflection W) z)
      ≡⟨ Tower.level3ReflectionDerived (levelReflection W) z ⟩
    Arithmetic.negateResidue (Tower.canonicalLevel3At L z)
  ∎

------------------------------------------------------------------------
-- 9. Exact j-value conjugation is a separate same-object weld.
------------------------------------------------------------------------

record JointJConjugation
    {R : Render.JPhaseRenderingAlgebra}
    {L : Tower.CanonicalLevel27Lift R}
    (W : JointReflectionAction R L) : Set₁ where
  field
    conjugateValue :
      Klein.Value (Render.klein R) →
      Klein.Value (Render.klein R)

    jConjugates :
      (z : Klein.Point (Render.klein R)) →
      Render.jValue R
        (Reflection.reflectPoint (phaseReflection W) z)
      ≡
      conjugateValue (Render.jValue R z)

open JointJConjugation public

jointRJConjugates :
  ∀ {R L}
    {W : JointReflectionAction R L} →
  (J : JointJConjugation W) →
  (z : Klein.Point (Render.klein R)) →
  exactJ
    (sampleAt L
      (Reflection.reflectPoint (phaseReflection W) z))
  ≡
  conjugateValue J (exactJ (sampleAt L z))
jointRJConjugates J z =
  jConjugates J z

------------------------------------------------------------------------
-- 10. Joint finite modular action: modular T is trivial on phase, +1 on level.
--
-- This is deliberately NOT the internal C3 phase cycle.  The distinction is
-- exactly what the phase/level no-go theorem requires.
------------------------------------------------------------------------

record JointFiniteState : Set where
  constructor joint-finite-state
  field
    finitePhase6 : Base.HexTruth
    finitePhase3 : Level.level3CuspFibre
    finiteLevel27 : Level.level27CuspFibre
    finiteLevel9 : Level.level9CuspFibre
    finiteLevel3 : Level.level3CuspFibre

open JointFiniteState public

jointFiniteT : JointFiniteState → JointFiniteState
jointFiniteT s =
  joint-finite-state
    (finitePhase6 s)
    (finitePhase3 s)
    (Level.translateTriadic Q.three (finiteLevel27 s))
    (Level.translateTriadic Q.two (finiteLevel9 s))
    (Level.translateTriadic Q.one (finiteLevel3 s))

jointFiniteTInverse : JointFiniteState → JointFiniteState
jointFiniteTInverse s =
  joint-finite-state
    (finitePhase6 s)
    (finitePhase3 s)
    (Arithmetic.addResidue
      (Arithmetic.negateResidue (Level.oneResidue Q.three))
      (finiteLevel27 s))
    (Arithmetic.addResidue
      (Arithmetic.negateResidue (Level.oneResidue Q.two))
      (finiteLevel9 s))
    (Arithmetic.addResidue
      (Arithmetic.negateResidue (Level.oneResidue Q.one))
      (finiteLevel3 s))

jointFiniteR : JointFiniteState → JointFiniteState
jointFiniteR s =
  joint-finite-state
    (Reflection.reflect6 (finitePhase6 s))
    (Arithmetic.negateResidue (finitePhase3 s))
    (Arithmetic.negateResidue (finiteLevel27 s))
    (Arithmetic.negateResidue (finiteLevel9 s))
    (Arithmetic.negateResidue (finiteLevel3 s))

phase6ReflectionInvolutive :
  (x : Base.HexTruth) →
  Reflection.reflect6 (Reflection.reflect6 x) ≡ x
phase6ReflectionInvolutive Base.hex-0 = refl
phase6ReflectionInvolutive Base.hex-1 = refl
phase6ReflectionInvolutive Base.hex-2 = refl
phase6ReflectionInvolutive Base.hex-3 = refl
phase6ReflectionInvolutive Base.hex-4 = refl
phase6ReflectionInvolutive Base.hex-5 = refl

jointFiniteDihedralPhase6 :
  (s : JointFiniteState) →
  finitePhase6
    (jointFiniteR (jointFiniteT (jointFiniteR s)))
  ≡
  finitePhase6 (jointFiniteTInverse s)
jointFiniteDihedralPhase6 s =
  phase6ReflectionInvolutive (finitePhase6 s)

jointFiniteDihedralPhase3 :
  (s : JointFiniteState) →
  finitePhase3
    (jointFiniteR (jointFiniteT (jointFiniteR s)))
  ≡
  finitePhase3 (jointFiniteTInverse s)
jointFiniteDihedralPhase3 s =
  Arithmetic.negateResidueInvolutive (finitePhase3 s)

jointFiniteDihedralLevel27 :
  (s : JointFiniteState) →
  finiteLevel27
    (jointFiniteR (jointFiniteT (jointFiniteR s)))
  ≡
  finiteLevel27 (jointFiniteTInverse s)
jointFiniteDihedralLevel27 s =
  Level.inversionConjugatesTranslationToInverse
    Level.canonicalCuspDihedralAt27
    (finiteLevel27 s)

jointFiniteDihedralLevel9 :
  (s : JointFiniteState) →
  finiteLevel9
    (jointFiniteR (jointFiniteT (jointFiniteR s)))
  ≡
  finiteLevel9 (jointFiniteTInverse s)
jointFiniteDihedralLevel9 s =
  Level.inversionConjugatesTranslationToInverse
    Level.canonicalCuspDihedralAt9
    (finiteLevel9 s)

jointFiniteDihedralLevel3 :
  (s : JointFiniteState) →
  finiteLevel3
    (jointFiniteR (jointFiniteT (jointFiniteR s)))
  ≡
  finiteLevel3 (jointFiniteTInverse s)
jointFiniteDihedralLevel3 s =
  Level.inversionConjugatesTranslationToInverse
    Level.canonicalCuspDihedralAt3
    (finiteLevel3 s)

record JointFiniteDihedralReceipt (s : JointFiniteState) : Set where
  constructor joint-finite-dihedral-receipt
  field
    phase6 :
      finitePhase6
        (jointFiniteR (jointFiniteT (jointFiniteR s)))
      ≡ finitePhase6 (jointFiniteTInverse s)

    phase3 :
      finitePhase3
        (jointFiniteR (jointFiniteT (jointFiniteR s)))
      ≡ finitePhase3 (jointFiniteTInverse s)

    level27 :
      finiteLevel27
        (jointFiniteR (jointFiniteT (jointFiniteR s)))
      ≡ finiteLevel27 (jointFiniteTInverse s)

    level9 :
      finiteLevel9
        (jointFiniteR (jointFiniteT (jointFiniteR s)))
      ≡ finiteLevel9 (jointFiniteTInverse s)

    level3 :
      finiteLevel3
        (jointFiniteR (jointFiniteT (jointFiniteR s)))
      ≡ finiteLevel3 (jointFiniteTInverse s)

canonicalJointFiniteDihedralReceipt :
  (s : JointFiniteState) →
  JointFiniteDihedralReceipt s
canonicalJointFiniteDihedralReceipt s =
  joint-finite-dihedral-receipt
    (jointFiniteDihedralPhase6 s)
    (jointFiniteDihedralPhase3 s)
    (jointFiniteDihedralLevel27 s)
    (jointFiniteDihedralLevel9 s)
    (jointFiniteDihedralLevel3 s)

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

    jointReflectionActionCompilerOwned : Bool
    reflectionNegatesPhaseC6 : Bool
    reflectionNegatesPhaseC3 : Bool
    reflectionNegatesLevelC27 : Bool
    reflectionNegatesLevelC9 : Bool
    reflectionNegatesLevelC3 : Bool
    exactJConjugationRequiresSameObjectWeld : Bool

    modularTIsIdentityOnPhaseLane : Bool
    modularTTranslatesLevelLane : Bool
    jointFiniteRTRIsTInverseCoordinatewise : Bool
    phaseInternalC3CycleIdentifiedWithModularT : Bool

    fullDeckGroupCollapsedToC27 : Bool

open JointPhaseLevelBoundary public

canonicalJointPhaseLevelBoundary : JointPhaseLevelBoundary
canonicalJointPhaseLevelBoundary =
  joint-phase-level-boundary
    true true true true
    true true true true
    true true true
    false
    true true true true true true true
    true true true false
    false
