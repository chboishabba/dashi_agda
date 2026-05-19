module DASHI.Physics.Closure.ChemistryRightLimitsInterpretationContract where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.AtomicPhotonuclearContactGateTheorem as APCGT
open import DASHI.Physics.Closure.ChemistryRightLimitsGateTheorem as CRLGT
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import DASHI.Physics.Closure.ShellDictionaryRecoveryGateTheorem as SDRGT
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Narrow non-cyclic interpretation contract for the current chemistry-facing
-- right-limits observable.
--
-- This surface does not strengthen the empirical photonuclear package into a
-- chemistry solver. It only says the current rightLimitGate can be read as a
-- stable, named, pre-spectral chemistry-facing observable class on the
-- current chemistry feature carrier.

record ChemistryRightLimitsInterpretationContract : Setω where
  field
    rightLimitsGate :
      CRLGT.ChemistryRightLimitsGateTheorem

    chemistryObservableName : String

    chemistryFacingObservable :
      CDQ.ChemistryFeature → Nat

    chemistryFacingObservableClass :
      CDQ.ChemistryFeature → Set

    chemistryFacingMeaning :
      Set

    interpretedObservableMatchesRightLimitGate :
      ∀ f →
      chemistryFacingObservable f
      ≡
      CRLGT.ChemistryRightLimitsGateTheorem.rightLimitGate
        rightLimitsGate
        f

    interpretationStable :
      ∀ f →
      chemistryFacingObservable
        (SDRGT.ShellDictionaryRecoveryGateTheorem.recoveryGate
          (CRLGT.ChemistryRightLimitsGateTheorem.shellDictionaryRecovery
            rightLimitsGate)
          f)
      ≡
      chemistryFacingObservable f

    defectChannelInterpretation :
      ∀ f →
      chemistryFacingObservableClass f
      ×
      (chemistryFacingObservable f
       ≡
       APCGT.AtomicPhotonuclearContactGateTheorem.defectChannelVisible
         (CRLGT.ChemistryRightLimitsGateTheorem.atomicPhotonuclearContact
           rightLimitsGate))

    empiricalBoundaryHeld :
      PEVS.PhotonuclearEmpiricalValidationSummary.nonClaimBoundary
        (APCGT.AtomicPhotonuclearContactGateTheorem.photonuclearValidationSummary
          (CRLGT.ChemistryRightLimitsGateTheorem.atomicPhotonuclearContact
            rightLimitsGate))
      ≡
      PEVS.empiricalOnlyValidation

    preSpectralBoundary : Set
    preScaleSettingBoundary : Set

    nonClaimBoundary : List String

canonicalChemistryRightLimitsInterpretationContract :
  ChemistryRightLimitsInterpretationContract
canonicalChemistryRightLimitsInterpretationContract =
  let
    gate =
      CRLGT.canonicalChemistryRightLimitsGateTheorem
    contact =
      CRLGT.ChemistryRightLimitsGateTheorem.atomicPhotonuclearContact
        gate
    observable =
      CRLGT.ChemistryRightLimitsGateTheorem.rightLimitGate
        gate
  in
  record
    { rightLimitsGate = gate
    ; chemistryObservableName =
        "closed-shell defect-channel pre-spectral observable"
    ; chemistryFacingObservable = observable
    ; chemistryFacingObservableClass =
        λ f →
        observable f
        ≡
        APCGT.AtomicPhotonuclearContactGateTheorem.defectChannelVisible
          contact
    ; chemistryFacingMeaning =
        CRLGT.ChemistryRightLimitsGateTheorem.closedShellChemistryVisible
          gate
    ; interpretedObservableMatchesRightLimitGate =
        λ _ → refl
    ; interpretationStable =
        CRLGT.ChemistryRightLimitsGateTheorem.rightLimitGateStable
          gate
    ; defectChannelInterpretation =
        λ f →
        refl
        ,
        refl
    ; empiricalBoundaryHeld = refl
    ; preSpectralBoundary =
        CRLGT.ChemistryRightLimitsGateTheorem.preSpectralBoundary
          gate
    ; preScaleSettingBoundary =
        CRLGT.ChemistryRightLimitsGateTheorem.preScaleSettingBoundary
          gate
    ; nonClaimBoundary =
        "ChemistryRightLimitsInterpretationContract only assigns a named chemistry-facing meaning to the current rightLimitGate"
        ∷ "The interpretation remains pre-spectral and pre-scale-setting, and keeps the photonuclear surface empirical-only"
        ∷ "It does not prove spectra, scale-setting, ionization energies, bonding, periodic-table structure, nuclear dynamics, or finished chemistry"
        ∷ []
    }
