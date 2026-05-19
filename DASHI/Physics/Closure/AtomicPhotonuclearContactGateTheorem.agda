module DASHI.Physics.Closure.AtomicPhotonuclearContactGateTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShellDictionaryRecoveryGateTheorem as SDRGT
open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.PhotonuclearEmpiricalMeasurementSurface as PEMS
open import DASHI.Physics.Closure.PhotonuclearEmpiricalEvidenceSummary as PEES
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest honest atomic -> photonuclear contact gate.
--
-- This theorem does not derive nuclear dynamics, QCD, collider cross-sections,
-- or chemistry. It only says the currently recovered shell/dictionary gate can
-- be read against the canonical repo-native photonuclear empirical package in
-- a stable, empirical-only way.

record AtomicPhotonuclearContactGateTheorem : Setω where
  field
    shellDictionaryRecovery :
      SDRGT.ShellDictionaryRecoveryGateTheorem

    photonuclearMeasurementSurface :
      PEMS.PhotonuclearEmpiricalMeasurementSurface Nat
    photonuclearEvidenceSummary :
      PEES.PhotonuclearEvidenceSummary Nat
    photonuclearValidationSummary :
      PEVS.PhotonuclearEmpiricalValidationSummary Nat

    atomicMeasurementContactGate :
      CDQ.ChemistryFeature → Nat

    atomicMeasurementContactStable :
      ∀ f →
      atomicMeasurementContactGate
        (SDRGT.ShellDictionaryRecoveryGateTheorem.recoveryGate
          shellDictionaryRecovery
          f)
      ≡
      atomicMeasurementContactGate f

    defectChannelVisible : Nat
    promotedObservableVisible : Nat
    densityProxyVisible : Nat

    atomicMeasurementContactVisible :
      ∀ f →
      atomicMeasurementContactGate f ≡ defectChannelVisible

    measurementClassContact : Set

    empiricalBoundaryHeld :
      PEVS.PhotonuclearEmpiricalValidationSummary.nonClaimBoundary
        photonuclearValidationSummary
      ≡
      PEVS.empiricalOnlyValidation

    nonClaimBoundary : List String

canonicalAtomicPhotonuclearContactGateTheorem :
  AtomicPhotonuclearContactGateTheorem
canonicalAtomicPhotonuclearContactGateTheorem =
  let
    recovery =
      SDRGT.canonicalShellDictionaryRecoveryGateTheorem
    surface = DDSI.photonuclearMeasurementSurfaceNat
    evidence = DDSI.photonuclearEvidenceSummaryNat
    validation = DDSI.photonuclearValidationSummaryNat
    observables =
      PEMS.PhotonuclearEmpiricalMeasurementSurface.measuredObservables
        surface
    defect =
      PEMS.PhotonuclearMeasuredObservables.defectIntensity observables
    promoted =
      PEMS.PhotonuclearMeasuredObservables.promotedObservable observables
    density =
      PEMS.PhotonuclearMeasuredObservables.densityProxy observables
  in
  record
    { shellDictionaryRecovery = recovery
    ; photonuclearMeasurementSurface = surface
    ; photonuclearEvidenceSummary = evidence
    ; photonuclearValidationSummary = validation
    ; atomicMeasurementContactGate = λ _ → defect
    ; atomicMeasurementContactStable = λ _ → refl
    ; defectChannelVisible = defect
    ; promotedObservableVisible = promoted
    ; densityProxyVisible = density
    ; atomicMeasurementContactVisible = λ _ → refl
    ; measurementClassContact =
        (f : CDQ.ChemistryFeature) →
        (λ _ → defect) f ≡ defect
    ; empiricalBoundaryHeld = refl
    ; nonClaimBoundary =
        "AtomicPhotonuclearContactGateTheorem only packages empirical contact between the current shell/dictionary recovery gate and the canonical photonuclear measurement surface"
        ∷ "It does not derive nuclear dynamics, QCD, collider cross-sections, spectra, scale-setting, bonding, or finished chemistry"
        ∷ "The atomicMeasurementContactGate is a stable empirical contact map on the current packaged observables, not a physics solver"
        ∷ []
    }
