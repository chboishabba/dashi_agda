module DASHI.Moonshine.JInvariant369JointBundleLegacyFibreBridgeExact where

------------------------------------------------------------------------
-- TYPE-DISTINCT JOINT BUNDLE -> PRE-EXISTING SIGNED JOINT FIBRE
--
-- New authoritative architecture:
--   JInvariant369JointPhaseLevelBundleExact
--
-- Older finite signed fibre:
--   JInvariant369JointFibredObserverExact
--
-- The old fibre remains useful for signed-SSP residual/non-descent machinery,
-- but it does not separately store phase-C3 and level-C3.  This bridge is
-- therefore intentionally forgetful in one direction only:
--
--   (phase6, phaseC3, level27, level9, level3) + signed
--          -> (phase6, level27, signed)
--
-- The derived level-9/level-3 coordinates are proved to agree.  No theorem
-- identifies phase-C3 with level-C3.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369JointPhaseLevelBundleExact as Joint
import DASHI.Moonshine.JInvariant369JointFibredObserverExact as Legacy

------------------------------------------------------------------------
-- 1. Forgetful finite-fibre bridge.
------------------------------------------------------------------------

toLegacyFiniteFibre :
  ∀ {R} {L : Tower.CanonicalLevel27Lift R} →
  Joint.JLevel27Sample R L →
  Signed.SignedMultiplicity →
  Legacy.Joint369FiniteFibre
toLegacyFiniteFibre sample signed =
  Legacy.joint369FiniteFibre
    (Joint.phase6State sample)
    (Joint.levelResidue27 (Joint.level27State sample))
    signed

legacyLevel9Agrees :
  ∀ {R} {L : Tower.CanonicalLevel27Lift R}
    (sample : Joint.JLevel27Sample R L)
    (signed : Signed.SignedMultiplicity) →
  Legacy.jointLevel9 (toLegacyFiniteFibre sample signed)
  ≡
  Joint.levelResidue9 (Joint.level9State sample)
legacyLevel9Agrees sample signed =
  sym (Joint.level27DeterminesLevel9
    (Joint.point sample))

legacyLevel3Agrees :
  ∀ {R} {L : Tower.CanonicalLevel27Lift R}
    (sample : Joint.JLevel27Sample R L)
    (signed : Signed.SignedMultiplicity) →
  Legacy.jointLevel3 (toLegacyFiniteFibre sample signed)
  ≡
  Joint.levelResidue3 (Joint.level3State sample)
legacyLevel3Agrees sample signed =
  begin
    Legacy.jointLevel3 (toLegacyFiniteFibre sample signed)
      ≡⟨ cong
          DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact.level9To3CoveringProjection
          (legacyLevel9Agrees sample signed) ⟩
    DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact.level9To3CoveringProjection
      (Joint.levelResidue9 (Joint.level9State sample))
      ≡⟨ sym (Joint.level9DeterminesLevel3 (Joint.point sample)) ⟩
    Joint.levelResidue3 (Joint.level3State sample)
  ∎

------------------------------------------------------------------------
-- 2. The bridge deliberately has no phase-C3 recovery theorem.
------------------------------------------------------------------------

record LegacyBridgeBoundary : Set where
  constructor legacy-bridge-boundary
  field
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
    true true true true true
    false false false
