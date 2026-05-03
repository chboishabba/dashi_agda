module DASHI.Physics.Closure.ChemistryRightLimitsPromotedObservableCouplingLaw where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as ACRT
open import DASHI.Physics.Closure.AtomicChemistryRightLimitsAdapter as ACRLA
open import DASHI.Physics.Closure.AtomicPhotonuclearContactGateTheorem as APCGT
open import DASHI.Physics.Closure.ChemistryRightLimitsInterpretationContract as CRLIC
open import DASHI.Physics.Closure.ChemistryRightLimitsGateTheorem as CRLGT
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest pre-spectral coupling law beyond the adapted defect-channel
-- observable. This law adds one second observable channel only:
-- the promoted observable already exposed by the photonuclear contact surface.
--
-- It does not use densityProxyVisible, and it does not introduce spectra,
-- scale-setting, bonding, or finished chemistry.

record ChemistryRightLimitsPromotedObservableCouplingLaw : Setω where
  field
    atomicRightLimitsAdapter :
      ACRLA.AtomicChemistryRightLimitsAdapter

    defectObservableName : String
    promotedObservableName : String

    adaptedObservable :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          atomicRightLimitsAdapter)
      →
      CDQ.ChemistryFeature

    adaptedDefectObservable :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          atomicRightLimitsAdapter)
      →
      Nat

    adaptedPromotedObservable :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          atomicRightLimitsAdapter)
      →
      Nat

    defectObservableVisible :
      (support :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            atomicRightLimitsAdapter))
      →
      CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingObservableClass
        (ACRLA.AtomicChemistryRightLimitsAdapter.rightLimitsInterpretation
          atomicRightLimitsAdapter)
        (adaptedObservable support)

    promotedObservableVisible :
      (support :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            atomicRightLimitsAdapter))
      →
      adaptedPromotedObservable support
      ≡
      APCGT.AtomicPhotonuclearContactGateTheorem.promotedObservableVisible
        (CRLGT.ChemistryRightLimitsGateTheorem.atomicPhotonuclearContact
          (CRLIC.ChemistryRightLimitsInterpretationContract.rightLimitsGate
            (ACRLA.AtomicChemistryRightLimitsAdapter.rightLimitsInterpretation
              atomicRightLimitsAdapter)))

    coupledObservableClass :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          atomicRightLimitsAdapter)
      →
      Set

    couplingStable :
      (support :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            atomicRightLimitsAdapter))
      →
      coupledObservableClass support

    preSpectralBoundary : Set
    preScaleSettingBoundary : Set

    nonClaimBoundary : List String

canonicalChemistryRightLimitsPromotedObservableCouplingLaw :
  ChemistryRightLimitsPromotedObservableCouplingLaw
canonicalChemistryRightLimitsPromotedObservableCouplingLaw =
  let
    adapter =
      ACRLA.canonicalAtomicChemistryRightLimitsAdapter
    contract =
      ACRLA.AtomicChemistryRightLimitsAdapter.rightLimitsInterpretation
        adapter
    gate =
      CRLIC.ChemistryRightLimitsInterpretationContract.rightLimitsGate
        contract
    contact =
      CRLGT.ChemistryRightLimitsGateTheorem.atomicPhotonuclearContact
        gate
    lift =
      ACRLA.AtomicChemistryRightLimitsAdapter.chemistrySupportToFeature
        adapter
    defect =
      CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingObservable
        contract
    promoted =
      APCGT.AtomicPhotonuclearContactGateTheorem.promotedObservableVisible
        contact
  in
  record
    { atomicRightLimitsAdapter = adapter
    ; defectObservableName =
        CRLIC.ChemistryRightLimitsInterpretationContract.chemistryObservableName
          contract
    ; promotedObservableName =
        "promoted pre-spectral observable companion"
    ; adaptedObservable = lift
    ; adaptedDefectObservable =
        λ support → defect (lift support)
    ; adaptedPromotedObservable =
        λ _ → promoted
    ; defectObservableVisible =
        ACRLA.AtomicChemistryRightLimitsAdapter.mappedRightLimitsObservableVisible
          adapter
    ; promotedObservableVisible =
        λ _ → refl
    ; coupledObservableClass =
        λ support →
        CRLIC.ChemistryRightLimitsInterpretationContract.chemistryFacingObservableClass
          contract
          (lift support)
        ×
        (promoted ≡ promoted)
    ; couplingStable =
        λ support →
        ACRLA.AtomicChemistryRightLimitsAdapter.mappedRightLimitsObservableVisible
          adapter
          support
        ,
        refl
    ; preSpectralBoundary =
        ACRLA.AtomicChemistryRightLimitsAdapter.preSpectralBoundary
          adapter
    ; preScaleSettingBoundary =
        ACRLA.AtomicChemistryRightLimitsAdapter.preScaleSettingBoundary
          adapter
    ; nonClaimBoundary =
        "ChemistryRightLimitsPromotedObservableCouplingLaw only couples the adapted defect-channel observable with the promoted observable already exposed by the photonuclear contact surface"
        ∷ "It stays pre-spectral and pre-scale-setting, and does not use densityProxyVisible"
        ∷ "It does not prove spectra, scale-setting, ionization energies, bonding, periodic-table structure, nuclear dynamics, or finished chemistry"
        ∷ []
    }
