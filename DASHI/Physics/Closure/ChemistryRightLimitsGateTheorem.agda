module DASHI.Physics.Closure.ChemistryRightLimitsGateTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_)

open import DASHI.Physics.Closure.ShellDictionaryRecoveryGateTheorem as SDRGT
open import DASHI.Physics.Closure.AtomicPhotonuclearContactGateTheorem as APCGT
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest honest chemistry-facing right-limits gate beyond the current
-- shell/dictionary recovery and photonuclear empirical contact gates.
--
-- This theorem does not claim spectra, scale-setting, ionization energies,
-- bonding, periodic-table structure, or finished chemistry. It only says:
--
-- * the current shell/dictionary recovery gate is stable on the current
--   chemistry feature carrier;
-- * the current atomic/photonuclear contact gate is stable on that same
--   recovered carrier; and
-- * those two gates can be read together as a pre-spectral, pre-scale-setting
--   chemistry-facing compatibility surface.

record ChemistryRightLimitsGateTheorem : Setω where
  field
    shellDictionaryRecovery :
      SDRGT.ShellDictionaryRecoveryGateTheorem

    atomicPhotonuclearContact :
      APCGT.AtomicPhotonuclearContactGateTheorem

    rightLimitGate :
      CDQ.ChemistryFeature → Nat

    rightLimitGateStable :
      ∀ f →
      rightLimitGate
        (SDRGT.ShellDictionaryRecoveryGateTheorem.recoveryGate
          shellDictionaryRecovery
          f)
      ≡
      rightLimitGate f

    chemistryFacingCompatibility : Set

    closedShellChemistryVisible : Set

    empiricalBoundaryHeld :
      PEVS.PhotonuclearEmpiricalValidationSummary.nonClaimBoundary
        (APCGT.AtomicPhotonuclearContactGateTheorem.photonuclearValidationSummary
          atomicPhotonuclearContact)
      ≡
      PEVS.empiricalOnlyValidation

    preSpectralBoundary : Set
    preScaleSettingBoundary : Set

    nonClaimBoundary : List String

canonicalChemistryRightLimitsGateTheorem :
  ChemistryRightLimitsGateTheorem
canonicalChemistryRightLimitsGateTheorem =
  let
    recovery =
      SDRGT.canonicalShellDictionaryRecoveryGateTheorem
    contact =
      APCGT.canonicalAtomicPhotonuclearContactGateTheorem
    contact-gate =
      APCGT.AtomicPhotonuclearContactGateTheorem.atomicMeasurementContactGate
        contact
  in
  record
    { shellDictionaryRecovery = recovery
    ; atomicPhotonuclearContact = contact
    ; rightLimitGate = contact-gate
    ; rightLimitGateStable = λ _ → refl
    ; chemistryFacingCompatibility =
        (f : CDQ.ChemistryFeature) →
        contact-gate
          (SDRGT.ShellDictionaryRecoveryGateTheorem.recoveryGate
            recovery
            f)
        ≡
        contact-gate f
    ; closedShellChemistryVisible =
        (f : CDQ.ChemistryFeature) →
        SDRGT.ShellDictionaryRecoveryGateTheorem.recoveredDictionaryClass
          recovery
          f
        ×
        (contact-gate f ≡
         APCGT.AtomicPhotonuclearContactGateTheorem.defectChannelVisible
           contact)
    ; empiricalBoundaryHeld = refl
    ; preSpectralBoundary =
        (f : CDQ.ChemistryFeature) →
        contact-gate f ≡ contact-gate f
    ; preScaleSettingBoundary =
        (f : CDQ.ChemistryFeature) →
        APCGT.AtomicPhotonuclearContactGateTheorem.densityProxyVisible
          contact
        ≡
        APCGT.AtomicPhotonuclearContactGateTheorem.densityProxyVisible
          contact
    ; nonClaimBoundary =
        "ChemistryRightLimitsGateTheorem only packages a pre-spectral, pre-scale-setting compatibility surface between the current shell/dictionary recovery gate and the current photonuclear empirical contact gate"
        ∷ "It does not prove spectra, scale-setting, ionization energies, bonding, periodic-table structure, nuclear dynamics, or finished chemistry"
        ∷ "The rightLimitGate remains the current empirical contact map on the current chemistry feature carrier"
        ∷ []
    }
