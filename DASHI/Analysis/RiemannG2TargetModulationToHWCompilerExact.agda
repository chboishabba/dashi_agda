module DASHI.Analysis.RiemannG2TargetModulationToHWCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannAristotlePoleNearTargetModulationExact as Target
import DASHI.Analysis.RiemannAristotlePoleNearTranslationModulationIntertwinerExact as HT
import DASHI.Analysis.RiemannAristotlePoleNearWindowRestrictionResidualExact as HW

------------------------------------------------------------------------
-- FIXED TARGET/CUTOFF SPECTRAL IDENTIFICATION -> H_W
--
-- PoleNearTargetModulation already fixes one literal target and cutoff, and its
-- ModulationSpectralIdentification already states the exact selected spectral
-- decomposition
--
--   spectral = cluster + (finite near + far).
--
-- The historical H_W record is family-shaped.  For this fixed target/cutoff
-- instance, a singleton FullCarrier/RestrictedCarrier is the exact embedding:
-- there is one selected translated/windowed object and the four scalar channels
-- are precisely those in the existing spectral-identification receipt.
--
-- Thus H_W itself is not another mathematical theorem once the literal target
-- modulation and its exact spectral split are recovered.  The live theorem is
-- that exact ModulationSpectralIdentification on the real selected object.
------------------------------------------------------------------------

fixedSpectralIdentificationToHW :
  ∀ {space} →
  (H_T : HT.TargetTranslationModulationIntertwiner) →
  (m : Target.PoleNearTargetModulation space) →
  Target.ModulationSpectralIdentification space m →
  HW.PoleNearWindowRestriction H_T
fixedSpectralIdentificationToHW {space} H_T m identification =
  HW.pole-near-window-restriction
    ⊤
    ⊤
    (Weil.WeilTestSpace.Scalar space)
    (λ _ → Target.spectralValue identification)
    (λ _ → tt)
    (λ _ → Target.finitePoleNearSigned identification)
    (λ _ → Target.sameOrdinateCluster identification)
    (λ _ → Target.farZeroRemainder identification)
    (Target._⊕_ identification)
    (λ _ → Target.spectralIsClusterNearFar identification)
    ⊤
    (Target.poleTaperCarrierOwned m)
    (Target.preservesTargetRelativeGap identification)
    (Target.preservesMultiplicity identification)
    (Target.preservesNearOffFinset identification)
    ⊤
    (Target.identificationReference identification)

------------------------------------------------------------------------
-- Search consequence.
------------------------------------------------------------------------

data HWSearchAction : Set where
  rebuildWindowRestrictionInterface
  recoverLiteralPoleNearTargetModulation
  recoverExactSpectralClusterNearFarIdentification
  compileHistoricalHW
  proceedToFinitePhaseEvaluation
  : HWSearchAction

data SearchStatus : Set where
  live pruned downstream : SearchStatus

searchStatus : HWSearchAction → SearchStatus
searchStatus rebuildWindowRestrictionInterface = pruned
searchStatus recoverLiteralPoleNearTargetModulation = live
searchStatus recoverExactSpectralClusterNearFarIdentification = live
searchStatus compileHistoricalHW = downstream
searchStatus proceedToFinitePhaseEvaluation = downstream

windowInterfaceRebuildPruned :
  searchStatus rebuildWindowRestrictionInterface ≡ pruned
windowInterfaceRebuildPruned = refl

record TargetModulationToHWBoundary : Set where
  constructor target-modulation-to-hw-boundary
  field
    historicalHWNeedsIndependentFamilyConstructionForFixedTargetCutoff : Bool
    historicalHWNeedsIndependentFamilyConstructionForFixedTargetCutoffIsFalse :
      historicalHWNeedsIndependentFamilyConstructionForFixedTargetCutoff ≡ false

    exactSpectralClusterNearFarIdentityRemainsRequired : Bool
    exactSpectralClusterNearFarIdentityRemainsRequiredIsTrue :
      exactSpectralClusterNearFarIdentityRemainsRequired ≡ true

    singletonEmbeddingChangesTheSelectedMathematicalObject : Bool
    singletonEmbeddingChangesTheSelectedMathematicalObjectIsFalse :
      singletonEmbeddingChangesTheSelectedMathematicalObject ≡ false

    hWCompilerClosedConditionally : Bool
    hWCompilerClosedConditionallyIsTrue : hWCompilerClosedConditionally ≡ true

    spectralIdentificationRecoveredHere : Bool
    spectralIdentificationRecoveredHereIsFalse :
      spectralIdentificationRecoveredHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalTargetModulationToHWBoundary : TargetModulationToHWBoundary
canonicalTargetModulationToHWBoundary =
  target-modulation-to-hw-boundary
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "For one literal PoleNearTargetModulation, target and cutoff are already fixed. Its ModulationSpectralIdentification is exactly the consumer-relevant cluster + finite-near + far decomposition. Embed that one selected object as a singleton family and historical H_W is compiler output. Do not rebuild a generic window family merely to satisfy the old interface. The actual live payment is the exact spectral identification on the literal target/cutoff object; once owned, proceed to the finite phase-sensitive evaluation. RH is not derived."
