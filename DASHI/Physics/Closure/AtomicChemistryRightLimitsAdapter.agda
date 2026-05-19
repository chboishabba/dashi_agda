module DASHI.Physics.Closure.AtomicChemistryRightLimitsAdapter where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_)

open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as ACRT
open import DASHI.Physics.Closure.ChemistryRightLimitsInterpretationContract as CRLIC
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Minimal non-cyclic adapter between the older atom/chemistry owner and the
-- newer right-limits interpretation lane.
--
-- This adapter does not refactor the older owner, and it does not strengthen
-- the chemistry interpretation into spectra, scale-setting, bonding, or a
-- finished chemistry theorem. It only records the smallest compatibility seam:
--
-- * the old chemistry-support carrier can be mapped into the current
--   ChemistryFeature carrier;
-- * the new interpreted right-limits observable is visible on that mapped
--   carrier; and
-- * the old closed-shell recovery placeholder and the new chemistry-facing
--   meaning can be carried side-by-side without re-entering the owner cycle.

record AtomicChemistryRightLimitsAdapter : Setω where
  field
    atomicChemistryRecovery :
      ACRT.AtomicChemistryRecoveryTheorem

    rightLimitsInterpretation :
      CRLIC.ChemistryRightLimitsInterpretationContract

    chemistrySupportToFeature :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        atomicChemistryRecovery
      →
      CDQ.ChemistryFeature

    mappedRightLimitsObservableVisible :
      (support :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          atomicChemistryRecovery)
      →
      CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingObservableClass
        rightLimitsInterpretation
        (chemistrySupportToFeature support)

    closedShellMeaningCompatible : Set

    preSpectralBoundary : Set

    preScaleSettingBoundary : Set

    nonClaimBoundary : List String

canonicalAtomicChemistryRightLimitsAdapter :
  AtomicChemistryRightLimitsAdapter
canonicalAtomicChemistryRightLimitsAdapter =
  let
    atomic =
      ACRT.canonicalAtomicChemistryRecoveryTheorem
    contract =
      CRLIC.canonicalChemistryRightLimitsInterpretationContract
  in
  record
    { atomicChemistryRecovery = atomic
    ; rightLimitsInterpretation = contract
    ; chemistrySupportToFeature = λ support → support
    ; mappedRightLimitsObservableVisible = λ _ → refl
    ; closedShellMeaningCompatible =
        ACRT.AtomicChemistryRecoveryTheorem.closedShellRecovery
          atomic
        ×
        CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingMeaning
          contract
    ; preSpectralBoundary =
        CRLIC.ChemistryRightLimitsInterpretationContract.preSpectralBoundary
          contract
    ; preScaleSettingBoundary =
        CRLIC.ChemistryRightLimitsInterpretationContract.preScaleSettingBoundary
          contract
    ; nonClaimBoundary =
        "AtomicChemistryRightLimitsAdapter only exposes a non-cyclic compatibility seam between the older atom/chemistry owner and the newer right-limits interpretation lane"
        ∷ "It does not refactor the old owner, and it does not add spectra, scale-setting, bonding, periodic-table structure, nuclear dynamics, or finished chemistry"
        ∷ "The richer chemistry-facing law remains a separate later step"
        ∷ []
    }
