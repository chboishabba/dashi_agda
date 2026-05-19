module DASHI.Physics.Closure.ChemistryRightLimitsObservableLaw where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as ACRT
open import DASHI.Physics.Closure.AtomicChemistryRightLimitsAdapter as ACRLA
open import DASHI.Physics.Closure.ChemistryRightLimitsInterpretationContract as CRLIC
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest richer chemistry-facing sibling law after the right-limits
-- interpretation contract and adapter seam.
--
-- This law still stays pre-spectral and pre-scale-setting. It does not infer
-- spectra, energy levels, bonding, periodic-table structure, or a finished
-- chemistry theorem. It only promotes the current defect-channel reading from
-- "named interpretation" to a stable observable law on the adapted chemistry
-- support carrier.

record ChemistryRightLimitsObservableLaw : Setω where
  field
    atomicRightLimitsAdapter :
      ACRLA.AtomicChemistryRightLimitsAdapter

    observableLawName : String

    adaptedObservable :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          atomicRightLimitsAdapter)
      →
      CDQ.ChemistryFeature

    observableLawVisible :
      (support :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            atomicRightLimitsAdapter))
      →
      CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingObservableClass
        (ACRLA.AtomicChemistryRightLimitsAdapter.rightLimitsInterpretation
          atomicRightLimitsAdapter)
        (adaptedObservable support)

    observableLawStable :
      (support :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            atomicRightLimitsAdapter))
      →
      CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingObservable
        (ACRLA.AtomicChemistryRightLimitsAdapter.rightLimitsInterpretation
          atomicRightLimitsAdapter)
        (adaptedObservable support)
      ≡
      CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingObservable
        (ACRLA.AtomicChemistryRightLimitsAdapter.rightLimitsInterpretation
          atomicRightLimitsAdapter)
        (adaptedObservable support)

    closedShellObservableCompatibility :
      Set

    preSpectralBoundary :
      Set

    preScaleSettingBoundary :
      Set

    nonClaimBoundary : List String

canonicalChemistryRightLimitsObservableLaw :
  ChemistryRightLimitsObservableLaw
canonicalChemistryRightLimitsObservableLaw =
  let
    adapter =
      ACRLA.canonicalAtomicChemistryRightLimitsAdapter
    contract =
      ACRLA.AtomicChemistryRightLimitsAdapter.rightLimitsInterpretation
        adapter
    lift =
      ACRLA.AtomicChemistryRightLimitsAdapter.chemistrySupportToFeature
        adapter
  in
  record
    { atomicRightLimitsAdapter = adapter
    ; observableLawName =
        "adapted closed-shell defect-channel observable law"
    ; adaptedObservable = lift
    ; observableLawVisible =
        ACRLA.AtomicChemistryRightLimitsAdapter.mappedRightLimitsObservableVisible
          adapter
    ; observableLawStable = λ _ → refl
    ; closedShellObservableCompatibility =
        ACRLA.AtomicChemistryRightLimitsAdapter.closedShellMeaningCompatible
          adapter
        ×
        ((support :
          ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
            (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
              adapter))
         →
         CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingObservableClass
           contract
           (lift support))
    ; preSpectralBoundary =
        ACRLA.AtomicChemistryRightLimitsAdapter.preSpectralBoundary
          adapter
    ; preScaleSettingBoundary =
        ACRLA.AtomicChemistryRightLimitsAdapter.preScaleSettingBoundary
          adapter
    ; nonClaimBoundary =
        "ChemistryRightLimitsObservableLaw only promotes the current interpreted right-limits observable to a stable adapted observable law on the chemistry-support carrier"
        ∷ "It remains pre-spectral and pre-scale-setting, and does not prove spectra, scale-setting, ionization energies, bonding, periodic-table structure, nuclear dynamics, or finished chemistry"
        ∷ "Any richer chemistry-facing law beyond the defect-channel observable remains a later step"
        ∷ []
    }
