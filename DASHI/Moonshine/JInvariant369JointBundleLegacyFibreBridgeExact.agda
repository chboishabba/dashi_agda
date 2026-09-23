module DASHI.Moonshine.JInvariant369JointBundleLegacyFibreBridgeExact where

------------------------------------------------------------------------
-- TYPE-DISTINCT CANONICAL JOINT SAMPLE -> PRE-EXISTING SIGNED JOINT FIBRE
--
-- New authoritative architecture:
--   JInvariant369JointPhaseLevelBundleExact
--
-- Older finite signed fibre:
--   JInvariant369JointFibredObserverExact
--
-- The bridge is intentionally defined on the canonical sampleAt L z.
-- An arbitrary JLevel27Sample record does not itself assert that its stored
-- level-9/level-3 coordinates are the projections of its stored level-27
-- coordinate. Restricting this bridge to sampleAt keeps those coherence
-- equations theorem-backed rather than postulated.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact as Joint
import DASHI.Moonshine.JInvariant369JointFibredObserverExact as Legacy

------------------------------------------------------------------------
-- 1. Forgetful finite-fibre bridge from the canonical sample.
------------------------------------------------------------------------

toLegacyFiniteFibreAt :
  ∀ {R} →
  (L : Tower.CanonicalLevel27Lift R) →
  Klein.Point (Render.klein R) →
  Signed.SignedMultiplicity →
  Legacy.Joint369FiniteFibre
toLegacyFiniteFibreAt L z signed =
  Legacy.joint369FiniteFibre
    (Joint.phase6State (Joint.sampleAt L z))
    (Joint.levelResidue27
      (Joint.level27State (Joint.sampleAt L z)))
    signed

phase6PreservedAt :
  ∀ {R}
    (L : Tower.CanonicalLevel27Lift R)
    (z : Klein.Point (Render.klein R))
    (signed : Signed.SignedMultiplicity) →
  Legacy.phase6Coordinate (toLegacyFiniteFibreAt L z signed)
  ≡
  Joint.phase6State (Joint.sampleAt L z)
phase6PreservedAt L z signed = refl

level27PreservedAt :
  ∀ {R}
    (L : Tower.CanonicalLevel27Lift R)
    (z : Klein.Point (Render.klein R))
    (signed : Signed.SignedMultiplicity) →
  Legacy.level27Coordinate (toLegacyFiniteFibreAt L z signed)
  ≡
  Joint.levelResidue27
    (Joint.level27State (Joint.sampleAt L z))
level27PreservedAt L z signed = refl

legacyLevel9AgreesAt :
  ∀ {R}
    (L : Tower.CanonicalLevel27Lift R)
    (z : Klein.Point (Render.klein R))
    (signed : Signed.SignedMultiplicity) →
  Legacy.jointLevel9 (toLegacyFiniteFibreAt L z signed)
  ≡
  Joint.levelResidue9
    (Joint.level9State (Joint.sampleAt L z))
legacyLevel9AgreesAt L z signed =
  sym (Joint.level27DeterminesLevel9 z)

legacyLevel3AgreesAt :
  ∀ {R}
    (L : Tower.CanonicalLevel27Lift R)
    (z : Klein.Point (Render.klein R))
    (signed : Signed.SignedMultiplicity) →
  Legacy.jointLevel3 (toLegacyFiniteFibreAt L z signed)
  ≡
  Joint.levelResidue3
    (Joint.level3State (Joint.sampleAt L z))
legacyLevel3AgreesAt L z signed =
  begin
    Legacy.jointLevel3 (toLegacyFiniteFibreAt L z signed)
      ≡⟨ cong Level.level9To3CoveringProjection
          (legacyLevel9AgreesAt L z signed) ⟩
    Level.level9To3CoveringProjection
      (Joint.levelResidue9
        (Joint.level9State (Joint.sampleAt L z)))
      ≡⟨ sym (Joint.level9DeterminesLevel3 z) ⟩
    Joint.levelResidue3
      (Joint.level3State (Joint.sampleAt L z))
  ∎

------------------------------------------------------------------------
-- 2. The bridge deliberately has no phase-C3 recovery theorem.
------------------------------------------------------------------------

record LegacyBridgeBoundary : Set where
  constructor legacy-bridge-boundary
  field
    bridgeRestrictedToCanonicalSamples : Bool
    phase6Preserved : Bool
    level27Preserved : Bool
    signedSSPAttached : Bool
    derivedLevel9AgreementOwned : Bool
    derivedLevel3AgreementOwned : Bool

    phaseC3RecoveredFromLegacyLevel3 : Bool
    phaseC3IdentifiedWithLevelC3 : Bool
    legacyFibreMoreInformativeThanNewBundle : Bool

open LegacyBridgeBoundary public

canonicalLegacyBridgeBoundary : LegacyBridgeBoundary
canonicalLegacyBridgeBoundary =
  legacy-bridge-boundary
    true true true true true true
    false false false
