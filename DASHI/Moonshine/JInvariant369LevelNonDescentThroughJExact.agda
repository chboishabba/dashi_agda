module DASHI.Moonshine.JInvariant369LevelNonDescentThroughJExact where

------------------------------------------------------------------------
-- PRINCIPAL-LEVEL DATA DOES NOT DESCEND THROUGH j
--
-- This sharpens the existing phase-vs-level no-go.
--
-- The obstruction is not specific to hue or atan2.  It is categorical:
--
--   * modular T preserves j;
--   * the genuine principal-level cusp coordinate is translated by T;
--   * the translation has no fixed point.
--
-- Therefore no function of j alone can recover that level coordinate.
--
-- This is exactly the information-loss statement:
--
--     lifted modular point  --->  j-value
--
-- forgets the principal-level lift.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369ModularReplicationExact as Replication
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Separation
import DASHI.Foundations.TriadicFiniteQuotient as Q

------------------------------------------------------------------------
-- 1. Generic descent obstruction.
------------------------------------------------------------------------

record JFactorizationTranslationAttempt
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (Fibre : Set) : Set₁ where
  field
    translationMatrix :
      Replication.Matrix A

    levelAt :
      Klein.Point (Render.klein R) →
      Fibre

    translateFibre :
      Fibre → Fibre

    translationFixedPointFree :
      (x : Fibre) →
      translateFibre x ≡ x →
      Separation.Empty

    levelTranslates :
      (z : Klein.Point (Render.klein R)) →
      levelAt (Replication.act A translationMatrix z)
      ≡
      translateFibre (levelAt z)

    decodeFromJ :
      Klein.Value (Render.klein R) →
      Fibre

    levelFactorsThroughJ :
      (z : Klein.Point (Render.klein R)) →
      levelAt z
      ≡
      decodeFromJ (Render.jValue R z)

open JFactorizationTranslationAttempt public

factorizationThroughJForcesFixed :
  ∀ {R A Fibre} →
  (W : JFactorizationTranslationAttempt R A Fibre) →
  (z : Klein.Point (Render.klein R)) →
  translateFibre W (levelAt W z)
  ≡
  levelAt W z
factorizationThroughJForcesFixed {R} {A} W z =
  begin
    translateFibre W (levelAt W z)
      ≡⟨ sym (levelTranslates W z) ⟩
    levelAt W
      (Replication.act A (translationMatrix W) z)
      ≡⟨ levelFactorsThroughJ W
            (Replication.act A (translationMatrix W) z) ⟩
    decodeFromJ W
      (Render.jValue R
        (Replication.act A (translationMatrix W) z))
      ≡⟨ cong (decodeFromJ W)
            (Replication.jInvariant
              A (translationMatrix W) z) ⟩
    decodeFromJ W (Render.jValue R z)
      ≡⟨ sym (levelFactorsThroughJ W z) ⟩
    levelAt W z
  ∎

levelCannotFactorThroughJ :
  ∀ {R A Fibre} →
  JFactorizationTranslationAttempt R A Fibre →
  (z : Klein.Point (Render.klein R)) →
  Separation.Empty
levelCannotFactorThroughJ W z =
  translationFixedPointFree W
    (levelAt W z)
    (factorizationThroughJForcesFixed W z)

------------------------------------------------------------------------
-- 2. Canonical level-3 instance.
------------------------------------------------------------------------

record Level3FactorsThroughJ
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (L : Tower.CanonicalLevel27Lift R) : Set₁ where
  field
    translationMatrix :
      Replication.Matrix A

    level3Translates :
      (z : Klein.Point (Render.klein R)) →
      Tower.canonicalLevel3At L
        (Replication.act A translationMatrix z)
      ≡
      Level.translateTriadic Q.one
        (Tower.canonicalLevel3At L z)

    decodeLevel3FromJ :
      Klein.Value (Render.klein R) →
      Level.level3CuspFibre

    level3FactorsThroughJ :
      (z : Klein.Point (Render.klein R)) →
      Tower.canonicalLevel3At L z
      ≡
      decodeLevel3FromJ (Render.jValue R z)

open Level3FactorsThroughJ public

level3Attempt :
  ∀ {R A L} →
  Level3FactorsThroughJ R A L →
  JFactorizationTranslationAttempt
    R A Level.level3CuspFibre
level3Attempt {L = L} W =
  record
    { JFactorizationTranslationAttempt.translationMatrix =
        Level3FactorsThroughJ.translationMatrix W
    ; levelAt = Tower.canonicalLevel3At L
    ; translateFibre = Level.translateTriadic Q.one
    ; translationFixedPointFree =
        Separation.level3TranslationNoFixedPoint
    ; levelTranslates = level3Translates W
    ; decodeFromJ = decodeLevel3FromJ W
    ; levelFactorsThroughJ = level3FactorsThroughJ W
    }

level3CannotFactorThroughJ :
  ∀ {R A L} →
  Level3FactorsThroughJ R A L →
  (z : Klein.Point (Render.klein R)) →
  Separation.Empty
level3CannotFactorThroughJ W z =
  levelCannotFactorThroughJ (level3Attempt W) z

------------------------------------------------------------------------
-- 3. Canonical level-9 instance.
------------------------------------------------------------------------

record Level9FactorsThroughJ
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (L : Tower.CanonicalLevel27Lift R) : Set₁ where
  field
    translationMatrix :
      Replication.Matrix A

    level9Translates :
      (z : Klein.Point (Render.klein R)) →
      Tower.canonicalLevel9At L
        (Replication.act A translationMatrix z)
      ≡
      Level.translateTriadic Q.two
        (Tower.canonicalLevel9At L z)

    decodeLevel9FromJ :
      Klein.Value (Render.klein R) →
      Level.level9CuspFibre

    level9FactorsThroughJ :
      (z : Klein.Point (Render.klein R)) →
      Tower.canonicalLevel9At L z
      ≡
      decodeLevel9FromJ (Render.jValue R z)

open Level9FactorsThroughJ public

level9Attempt :
  ∀ {R A L} →
  Level9FactorsThroughJ R A L →
  JFactorizationTranslationAttempt
    R A Level.level9CuspFibre
level9Attempt {L = L} W =
  record
    { JFactorizationTranslationAttempt.translationMatrix =
        Level9FactorsThroughJ.translationMatrix W
    ; levelAt = Tower.canonicalLevel9At L
    ; translateFibre = Level.translateTriadic Q.two
    ; translationFixedPointFree =
        Separation.level9TranslationNoFixedPoint
    ; levelTranslates = level9Translates W
    ; decodeFromJ = decodeLevel9FromJ W
    ; levelFactorsThroughJ = level9FactorsThroughJ W
    }

level9CannotFactorThroughJ :
  ∀ {R A L} →
  Level9FactorsThroughJ R A L →
  (z : Klein.Point (Render.klein R)) →
  Separation.Empty
level9CannotFactorThroughJ W z =
  levelCannotFactorThroughJ (level9Attempt W) z

------------------------------------------------------------------------
-- 4. Canonical level-27 instance.
------------------------------------------------------------------------

record Level27FactorsThroughJ
    (R : Render.JPhaseRenderingAlgebra)
    (A : Replication.J369ModularAction R)
    (L : Tower.CanonicalLevel27Lift R) : Set₁ where
  field
    translationMatrix :
      Replication.Matrix A

    level27Translates :
      (z : Klein.Point (Render.klein R)) →
      Tower.level27At L
        (Replication.act A translationMatrix z)
      ≡
      Level.translateTriadic Q.three
        (Tower.level27At L z)

    decodeLevel27FromJ :
      Klein.Value (Render.klein R) →
      Level.level27CuspFibre

    level27FactorsThroughJ :
      (z : Klein.Point (Render.klein R)) →
      Tower.level27At L z
      ≡
      decodeLevel27FromJ (Render.jValue R z)

open Level27FactorsThroughJ public

level27Attempt :
  ∀ {R A L} →
  Level27FactorsThroughJ R A L →
  JFactorizationTranslationAttempt
    R A Level.level27CuspFibre
level27Attempt {L = L} W =
  record
    { JFactorizationTranslationAttempt.translationMatrix =
        Level27FactorsThroughJ.translationMatrix W
    ; levelAt = Tower.level27At L
    ; translateFibre = Level.translateTriadic Q.three
    ; translationFixedPointFree =
        Separation.level27TranslationNoFixedPoint
    ; levelTranslates = level27Translates W
    ; decodeFromJ = decodeLevel27FromJ W
    ; levelFactorsThroughJ = level27FactorsThroughJ W
    }

level27CannotFactorThroughJ :
  ∀ {R A L} →
  Level27FactorsThroughJ R A L →
  (z : Klein.Point (Render.klein R)) →
  Separation.Empty
level27CannotFactorThroughJ W z =
  levelCannotFactorThroughJ (level27Attempt W) z

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record LevelNonDescentThroughJBoundary : Set where
  constructor level-non-descent-through-j-boundary
  field
    genericTInvariantBaseNoDescentCompilerOwned : Bool
    level3CannotFactorThroughJOwned : Bool
    level9CannotFactorThroughJOwned : Bool
    level27CannotFactorThroughJOwned : Bool

    phaseReadoutCannotFactorThroughJ : Bool
    levelLiftRecoverableFromJAlone : Bool
    fullDeckGroupRecoveredFromJAlone : Bool

open LevelNonDescentThroughJBoundary public

canonicalLevelNonDescentThroughJBoundary :
  LevelNonDescentThroughJBoundary
canonicalLevelNonDescentThroughJBoundary =
  level-non-descent-through-j-boundary
    true true true true
    false false false
